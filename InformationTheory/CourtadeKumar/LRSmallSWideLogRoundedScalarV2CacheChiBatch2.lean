import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore

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

noncomputable def chi128Slice : ChiSlice :=
  { lo := (21/256), hi := (11/128) }

noncomputable def chi128LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (21/16) }, upper := { exponent := -4, mantissa := (11/8) } }

private noncomputable def chi128QChiValue : RationalEnclosure :=
  { lower := (-51328168205750121320896888345401242/258439601212559694594657087068561265), upper := (-995868934889849292058719701778639357785801825568128397457063/5375001274843884609209190911886533010454063610255408893338240) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi128QChiValue_eq :
    chi128QChiValue =
      (chi128Slice.qChiAD 8 chi128LogChiCertificate).value := by
  norm_num [chi128QChiValue, chi128LogChiCertificate, chi128Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi128LogChi_valid :
    (if chi128Slice.lo = 0 then
      if chi128Slice.hi = 0 then true
      else decide (chi128Slice.hi ≤ 1 / 4) &&
        chi128LogChiCertificate.check
          (IntervalAD.const chi128Slice.hi).value
    else chi128LogChiCertificate.check
      chi128Slice.chiAD.value) = true := by
  norm_num [chi128Slice, chi128LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi128ValidityFacts :
    ChiFacts chi128Slice chi128LogChiCertificate :=
  { domain := by norm_num [chi128Slice]
    onePlusPositive := by
      norm_num [chi128Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi128LogChi_valid }

noncomputable def chi128InputQChi : RationalEnclosure :=
  { lower := (-1666045/8388608), upper := (-3108447/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi128InputQChi_eq :
    chi128InputQChi = outerEnclosure 24 chi128QChiValue := by
  rfl'

theorem chi128RoundedFacts :
    ChiRoundedFacts 8 chi128Slice chi128LogChiCertificate
      chi128InputQChi :=
  { coversQChi := by
      rw [chi128InputQChi_eq, chi128QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi129Slice : ChiSlice :=
  { lo := (11/128), hi := (23/256) }

noncomputable def chi129LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (11/8) }, upper := { exponent := -4, mantissa := (23/16) } }

private noncomputable def chi129QChiValue : RationalEnclosure :=
  { lower := (-184618180692002396520847744361051/909270220069816564117733910144810), upper := (-62050429591780607779748419450891972415230599716465609/326737814158225460036080940101497697779969687114773760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi129QChiValue_eq :
    chi129QChiValue =
      (chi129Slice.qChiAD 8 chi129LogChiCertificate).value := by
  norm_num [chi129QChiValue, chi129LogChiCertificate, chi129Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi129LogChi_valid :
    (if chi129Slice.lo = 0 then
      if chi129Slice.hi = 0 then true
      else decide (chi129Slice.hi ≤ 1 / 4) &&
        chi129LogChiCertificate.check
          (IntervalAD.const chi129Slice.hi).value
    else chi129LogChiCertificate.check
      chi129Slice.chiAD.value) = true := by
  norm_num [chi129Slice, chi129LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi129ValidityFacts :
    ChiFacts chi129Slice chi129LogChiCertificate :=
  { domain := by norm_num [chi129Slice]
    onePlusPositive := by
      norm_num [chi129Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi129LogChi_valid }

noncomputable def chi129InputQChi : RationalEnclosure :=
  { lower := (-1703223/8388608), upper := (-3186143/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi129InputQChi_eq :
    chi129InputQChi = outerEnclosure 24 chi129QChiValue := by
  rfl'

theorem chi129RoundedFacts :
    ChiRoundedFacts 8 chi129Slice chi129LogChiCertificate
      chi129InputQChi :=
  { coversQChi := by
      rw [chi129InputQChi_eq, chi129QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi130Slice : ChiSlice :=
  { lo := (23/256), hi := (3/32) }

noncomputable def chi130LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (23/16) }, upper := { exponent := -4, mantissa := (3/2) } }

private noncomputable def chi130QChiValue : RationalEnclosure :=
  { lower := (-1090209053779101912892858376/5259479650587918944110361439), upper := (-6288623084009481673528144297105710952077973/32358126756546766941303981509472656250000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi130QChiValue_eq :
    chi130QChiValue =
      (chi130Slice.qChiAD 8 chi130LogChiCertificate).value := by
  norm_num [chi130QChiValue, chi130LogChiCertificate, chi130Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi130LogChi_valid :
    (if chi130Slice.lo = 0 then
      if chi130Slice.hi = 0 then true
      else decide (chi130Slice.hi ≤ 1 / 4) &&
        chi130LogChiCertificate.check
          (IntervalAD.const chi130Slice.hi).value
    else chi130LogChiCertificate.check
      chi130Slice.chiAD.value) = true := by
  norm_num [chi130Slice, chi130LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi130ValidityFacts :
    ChiFacts chi130Slice chi130LogChiCertificate :=
  { domain := by norm_num [chi130Slice]
    onePlusPositive := by
      norm_num [chi130Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi130LogChi_valid }

noncomputable def chi130InputQChi : RationalEnclosure :=
  { lower := (-3477659/16777216), upper := (-3260559/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi130InputQChi_eq :
    chi130InputQChi = outerEnclosure 24 chi130QChiValue := by
  rfl'

theorem chi130RoundedFacts :
    ChiRoundedFacts 8 chi130Slice chi130LogChiCertificate
      chi130InputQChi :=
  { coversQChi := by
      rw [chi130InputQChi_eq, chi130QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi131Slice : ChiSlice :=
  { lo := (3/32), hi := (25/256) }

noncomputable def chi131LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (3/2) }, upper := { exponent := -4, mantissa := (25/16) } }

private noncomputable def chi131QChiValue : RationalEnclosure :=
  { lower := (-15563783192208241930811/73639739757568359375000), upper := (-20449926201626747919068822803731438165522739729278503/102973718063898198374770233545318162036718750000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi131QChiValue_eq :
    chi131QChiValue =
      (chi131Slice.qChiAD 8 chi131LogChiCertificate).value := by
  norm_num [chi131QChiValue, chi131LogChiCertificate, chi131Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi131LogChi_valid :
    (if chi131Slice.lo = 0 then
      if chi131Slice.hi = 0 then true
      else decide (chi131Slice.hi ≤ 1 / 4) &&
        chi131LogChiCertificate.check
          (IntervalAD.const chi131Slice.hi).value
    else chi131LogChiCertificate.check
      chi131Slice.chiAD.value) = true := by
  norm_num [chi131Slice, chi131LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi131ValidityFacts :
    ChiFacts chi131Slice chi131LogChiCertificate :=
  { domain := by norm_num [chi131Slice]
    onePlusPositive := by
      norm_num [chi131Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi131LogChi_valid }

noncomputable def chi131InputQChi : RationalEnclosure :=
  { lower := (-3545871/16777216), upper := (-416481/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi131InputQChi_eq :
    chi131InputQChi = outerEnclosure 24 chi131QChiValue := by
  rfl'

theorem chi131RoundedFacts :
    ChiRoundedFacts 8 chi131Slice chi131LogChiCertificate
      chi131InputQChi :=
  { coversQChi := by
      rw [chi131InputQChi_eq, chi131QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi132Slice : ChiSlice :=
  { lo := (25/256), hi := (13/128) }

noncomputable def chi132LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (25/16) }, upper := { exponent := -4, mantissa := (13/8) } }

private noncomputable def chi132QChiValue : RationalEnclosure :=
  { lower := (-311765485869461357427908449161249926/1448421528810875757359405482835244477), upper := (-5771483187967017802701307682445877263473679909389/28477965604258923561592706819977977849439992785280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi132QChiValue_eq :
    chi132QChiValue =
      (chi132Slice.qChiAD 8 chi132LogChiCertificate).value := by
  norm_num [chi132QChiValue, chi132LogChiCertificate, chi132Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi132LogChi_valid :
    (if chi132Slice.lo = 0 then
      if chi132Slice.hi = 0 then true
      else decide (chi132Slice.hi ≤ 1 / 4) &&
        chi132LogChiCertificate.check
          (IntervalAD.const chi132Slice.hi).value
    else chi132LogChiCertificate.check
      chi132Slice.chiAD.value) = true := by
  norm_num [chi132Slice, chi132LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi132ValidityFacts :
    ChiFacts chi132Slice chi132LogChiCertificate :=
  { domain := by norm_num [chi132Slice]
    onePlusPositive := by
      norm_num [chi132Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi132LogChi_valid }

noncomputable def chi132InputQChi : RationalEnclosure :=
  { lower := (-902803/4194304), upper := (-425019/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi132InputQChi_eq :
    chi132InputQChi = outerEnclosure 24 chi132QChiValue := by
  rfl'

theorem chi132RoundedFacts :
    ChiRoundedFacts 8 chi132Slice chi132LogChiCertificate
      chi132InputQChi :=
  { coversQChi := by
      rw [chi132InputQChi_eq, chi132QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi133Slice : ChiSlice :=
  { lo := (11/64), hi := (45/256) }

noncomputable def chi133LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (11/8) }, upper := { exponent := -3, mantissa := (45/32) } }

private noncomputable def chi133QChiValue : RationalEnclosure :=
  { lower := (-7679682584249680027251526086109/29073388331568874951806040292400), upper := (-47122836223990192571793157324225748087131495638821092510733021/185462769420590134832691430003858403581243895104957355910988800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi133QChiValue_eq :
    chi133QChiValue =
      (chi133Slice.qChiAD 8 chi133LogChiCertificate).value := by
  norm_num [chi133QChiValue, chi133LogChiCertificate, chi133Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi133LogChi_valid :
    (if chi133Slice.lo = 0 then
      if chi133Slice.hi = 0 then true
      else decide (chi133Slice.hi ≤ 1 / 4) &&
        chi133LogChiCertificate.check
          (IntervalAD.const chi133Slice.hi).value
    else chi133LogChiCertificate.check
      chi133Slice.chiAD.value) = true := by
  norm_num [chi133Slice, chi133LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi133ValidityFacts :
    ChiFacts chi133Slice chi133LogChiCertificate :=
  { domain := by norm_num [chi133Slice]
    onePlusPositive := by
      norm_num [chi133Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi133LogChi_valid }

noncomputable def chi133InputQChi : RationalEnclosure :=
  { lower := (-553959/2097152), upper := (-1065699/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi133InputQChi_eq :
    chi133InputQChi = outerEnclosure 24 chi133QChiValue := by
  rfl'

theorem chi133RoundedFacts :
    ChiRoundedFacts 8 chi133Slice chi133LogChiCertificate
      chi133InputQChi :=
  { coversQChi := by
      rw [chi133InputQChi_eq, chi133QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi134Slice : ChiSlice :=
  { lo := (45/256), hi := (23/128) }

noncomputable def chi134LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (45/32) }, upper := { exponent := -3, mantissa := (23/16) } }

private noncomputable def chi134QChiValue : RationalEnclosure :=
  { lower := (-2958416564652544626528385946560463865689/11134982691260011285512455629048607172630), upper := (-383388432391909084777112990260584949079893493891915839260853/1499228671799928972249329079339473639410083830293855962812160) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi134QChiValue_eq :
    chi134QChiValue =
      (chi134Slice.qChiAD 8 chi134LogChiCertificate).value := by
  norm_num [chi134QChiValue, chi134LogChiCertificate, chi134Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi134LogChi_valid :
    (if chi134Slice.lo = 0 then
      if chi134Slice.hi = 0 then true
      else decide (chi134Slice.hi ≤ 1 / 4) &&
        chi134LogChiCertificate.check
          (IntervalAD.const chi134Slice.hi).value
    else chi134LogChiCertificate.check
      chi134Slice.chiAD.value) = true := by
  norm_num [chi134Slice, chi134LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi134ValidityFacts :
    ChiFacts chi134Slice chi134LogChiCertificate :=
  { domain := by norm_num [chi134Slice]
    onePlusPositive := by
      norm_num [chi134Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi134LogChi_valid }

noncomputable def chi134InputQChi : RationalEnclosure :=
  { lower := (-4457483/16777216), upper := (-4290333/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi134InputQChi_eq :
    chi134InputQChi = outerEnclosure 24 chi134QChiValue := by
  rfl'

theorem chi134RoundedFacts :
    ChiRoundedFacts 8 chi134Slice chi134LogChiCertificate
      chi134InputQChi :=
  { coversQChi := by
      rw [chi134InputQChi_eq, chi134QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi135Slice : ChiSlice :=
  { lo := (23/128), hi := (47/256) }

noncomputable def chi135LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (23/16) }, upper := { exponent := -3, mantissa := (47/32) } }

private noncomputable def chi135QChiValue : RationalEnclosure :=
  { lower := (-273754886209003912179960978883/1024750228695194529755696228760), upper := (-2333625685347974694798421133932819919041926480673783834179517519/9070340671604535525486875906229272622308705189500937509241617920) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi135QChiValue_eq :
    chi135QChiValue =
      (chi135Slice.qChiAD 8 chi135LogChiCertificate).value := by
  norm_num [chi135QChiValue, chi135LogChiCertificate, chi135Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi135LogChi_valid :
    (if chi135Slice.lo = 0 then
      if chi135Slice.hi = 0 then true
      else decide (chi135Slice.hi ≤ 1 / 4) &&
        chi135LogChiCertificate.check
          (IntervalAD.const chi135Slice.hi).value
    else chi135LogChiCertificate.check
      chi135Slice.chiAD.value) = true := by
  norm_num [chi135Slice, chi135LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi135ValidityFacts :
    ChiFacts chi135Slice chi135LogChiCertificate :=
  { domain := by norm_num [chi135Slice]
    onePlusPositive := by
      norm_num [chi135Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi135LogChi_valid }

noncomputable def chi135InputQChi : RationalEnclosure :=
  { lower := (-4481917/16777216), upper := (-4316457/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi135InputQChi_eq :
    chi135InputQChi = outerEnclosure 24 chi135QChiValue := by
  rfl'

theorem chi135RoundedFacts :
    ChiRoundedFacts 8 chi135Slice chi135LogChiCertificate
      chi135InputQChi :=
  { coversQChi := by
      rw [chi135InputQChi_eq, chi135QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi136Slice : ChiSlice :=
  { lo := (47/256), hi := (3/16) }

noncomputable def chi136LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (47/32) }, upper := { exponent := -3, mantissa := (3/2) } }

private noncomputable def chi136QChiValue : RationalEnclosure :=
  { lower := (-56744871391702708955872676951377966469284/211324887159828985553350047453090869488965), upper := (-128160112456753172945107350366630868460067728042175227/495292704280849184890664173718181725364761718750000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi136QChiValue_eq :
    chi136QChiValue =
      (chi136Slice.qChiAD 8 chi136LogChiCertificate).value := by
  norm_num [chi136QChiValue, chi136LogChiCertificate, chi136Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi136LogChi_valid :
    (if chi136Slice.lo = 0 then
      if chi136Slice.hi = 0 then true
      else decide (chi136Slice.hi ≤ 1 / 4) &&
        chi136LogChiCertificate.check
          (IntervalAD.const chi136Slice.hi).value
    else chi136LogChiCertificate.check
      chi136Slice.chiAD.value) = true := by
  norm_num [chi136Slice, chi136LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi136ValidityFacts :
    ChiFacts chi136Slice chi136LogChiCertificate :=
  { domain := by norm_num [chi136Slice]
    onePlusPositive := by
      norm_num [chi136Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi136LogChi_valid }

noncomputable def chi136InputQChi : RationalEnclosure :=
  { lower := (-1126253/4194304), upper := (-2170605/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi136InputQChi_eq :
    chi136InputQChi = outerEnclosure 24 chi136QChiValue := by
  rfl'

theorem chi136RoundedFacts :
    ChiRoundedFacts 8 chi136Slice chi136LogChiCertificate
      chi136InputQChi :=
  { coversQChi := by
      rw [chi136InputQChi_eq, chi136QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi137Slice : ChiSlice :=
  { lo := (0), hi := (1/128) }

noncomputable def chi137LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -7, mantissa := (1) }, upper := { exponent := -7, mantissa := (1) } }

private noncomputable def chi137QChiValue : RationalEnclosure :=
  { lower := (-597351034279/15881657245740), upper := (0) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi137QChiValue_eq :
    chi137QChiValue =
      (chi137Slice.qChiAD 8 chi137LogChiCertificate).value := by
  norm_num [chi137QChiValue, chi137LogChiCertificate, chi137Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi137LogChi_valid :
    (if chi137Slice.lo = 0 then
      if chi137Slice.hi = 0 then true
      else decide (chi137Slice.hi ≤ 1 / 4) &&
        chi137LogChiCertificate.check
          (IntervalAD.const chi137Slice.hi).value
    else chi137LogChiCertificate.check
      chi137Slice.chiAD.value) = true := by
  norm_num [chi137Slice, chi137LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi137ValidityFacts :
    ChiFacts chi137Slice chi137LogChiCertificate :=
  { domain := by norm_num [chi137Slice]
    onePlusPositive := by
      norm_num [chi137Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi137LogChi_valid }

noncomputable def chi137InputQChi : RationalEnclosure :=
  { lower := (-157759/4194304), upper := (0) }

set_option maxRecDepth 1000000 in
private theorem chi137InputQChi_eq :
    chi137InputQChi = outerEnclosure 24 chi137QChiValue := by
  rfl'

theorem chi137RoundedFacts :
    ChiRoundedFacts 8 chi137Slice chi137LogChiCertificate
      chi137InputQChi :=
  { coversQChi := by
      rw [chi137InputQChi_eq, chi137QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi138Slice : ChiSlice :=
  { lo := (1/128), hi := (1/64) }

noncomputable def chi138LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -7, mantissa := (1) }, upper := { exponent := -6, mantissa := (1) } }

private noncomputable def chi138QChiValue : RationalEnclosure :=
  { lower := (-597351034279/7940828622870), upper := (-18517881293419/635266289829600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi138QChiValue_eq :
    chi138QChiValue =
      (chi138Slice.qChiAD 8 chi138LogChiCertificate).value := by
  norm_num [chi138QChiValue, chi138LogChiCertificate, chi138Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi138LogChi_valid :
    (if chi138Slice.lo = 0 then
      if chi138Slice.hi = 0 then true
      else decide (chi138Slice.hi ≤ 1 / 4) &&
        chi138LogChiCertificate.check
          (IntervalAD.const chi138Slice.hi).value
    else chi138LogChiCertificate.check
      chi138Slice.chiAD.value) = true := by
  norm_num [chi138Slice, chi138LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi138ValidityFacts :
    ChiFacts chi138Slice chi138LogChiCertificate :=
  { domain := by norm_num [chi138Slice]
    onePlusPositive := by
      norm_num [chi138Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi138LogChi_valid }

noncomputable def chi138InputQChi : RationalEnclosure :=
  { lower := (-1262071/16777216), upper := (-122263/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi138InputQChi_eq :
    chi138InputQChi = outerEnclosure 24 chi138QChiValue := by
  rfl'

theorem chi138RoundedFacts :
    ChiRoundedFacts 8 chi138Slice chi138LogChiCertificate
      chi138InputQChi :=
  { coversQChi := by
      rw [chi138InputQChi_eq, chi138QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi139Slice : ChiSlice :=
  { lo := (1/32), hi := (9/256) }

noncomputable def chi139LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (1) }, upper := { exponent := -5, mantissa := (9/8) } }

private noncomputable def chi139QChiValue : RationalEnclosure :=
  { lower := (-597351034279/5055866079264), upper := (-16375282563138350701198619883977447/162427227535797212269098250277644800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi139QChiValue_eq :
    chi139QChiValue =
      (chi139Slice.qChiAD 8 chi139LogChiCertificate).value := by
  norm_num [chi139QChiValue, chi139LogChiCertificate, chi139Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi139LogChi_valid :
    (if chi139Slice.lo = 0 then
      if chi139Slice.hi = 0 then true
      else decide (chi139Slice.hi ≤ 1 / 4) &&
        chi139LogChiCertificate.check
          (IntervalAD.const chi139Slice.hi).value
    else chi139LogChiCertificate.check
      chi139Slice.chiAD.value) = true := by
  norm_num [chi139Slice, chi139LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi139ValidityFacts :
    ChiFacts chi139Slice chi139LogChiCertificate :=
  { domain := by norm_num [chi139Slice]
    onePlusPositive := by
      norm_num [chi139Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi139LogChi_valid }

noncomputable def chi139InputQChi : RationalEnclosure :=
  { lower := (-991115/8388608), upper := (-1691413/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi139InputQChi_eq :
    chi139InputQChi = outerEnclosure 24 chi139QChiValue := by
  rfl'

theorem chi139RoundedFacts :
    ChiRoundedFacts 8 chi139Slice chi139LogChiCertificate
      chi139InputQChi :=
  { coversQChi := by
      rw [chi139InputQChi_eq, chi139QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi140Slice : ChiSlice :=
  { lo := (9/256), hi := (5/128) }

noncomputable def chi140LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (9/8) }, upper := { exponent := -5, mantissa := (5/4) } }

private noncomputable def chi140QChiValue : RationalEnclosure :=
  { lower := (-8258806963621196338134285677587/65370806536660809862089731409090), upper := (-12779809500257751177945080333562460089133/116728842036742513045167265271254747598400) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi140QChiValue_eq :
    chi140QChiValue =
      (chi140Slice.qChiAD 8 chi140LogChiCertificate).value := by
  norm_num [chi140QChiValue, chi140LogChiCertificate, chi140Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi140LogChi_valid :
    (if chi140Slice.lo = 0 then
      if chi140Slice.hi = 0 then true
      else decide (chi140Slice.hi ≤ 1 / 4) &&
        chi140LogChiCertificate.check
          (IntervalAD.const chi140Slice.hi).value
    else chi140LogChiCertificate.check
      chi140Slice.chiAD.value) = true := by
  norm_num [chi140Slice, chi140LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi140ValidityFacts :
    ChiFacts chi140Slice chi140LogChiCertificate :=
  { domain := by norm_num [chi140Slice]
    onePlusPositive := by
      norm_num [chi140Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi140LogChi_valid }

noncomputable def chi140InputQChi : RationalEnclosure :=
  { lower := (-1059799/8388608), upper := (-1836817/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi140InputQChi_eq :
    chi140InputQChi = outerEnclosure 24 chi140QChiValue := by
  rfl'

theorem chi140RoundedFacts :
    ChiRoundedFacts 8 chi140Slice chi140LogChiCertificate
      chi140InputQChi :=
  { coversQChi := by
      rw [chi140InputQChi_eq, chi140QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi141Slice : ChiSlice :=
  { lo := (1/64), hi := (5/256) }

noncomputable def chi141LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -6, mantissa := (1) }, upper := { exponent := -6, mantissa := (5/4) } }

private noncomputable def chi141QChiValue : RationalEnclosure :=
  { lower := (-597351034279/7468893071640), upper := (-8928846126732840480229/149181269292446122892160) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi141QChiValue_eq :
    chi141QChiValue =
      (chi141Slice.qChiAD 8 chi141LogChiCertificate).value := by
  norm_num [chi141QChiValue, chi141LogChiCertificate, chi141Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi141LogChi_valid :
    (if chi141Slice.lo = 0 then
      if chi141Slice.hi = 0 then true
      else decide (chi141Slice.hi ≤ 1 / 4) &&
        chi141LogChiCertificate.check
          (IntervalAD.const chi141Slice.hi).value
    else chi141LogChiCertificate.check
      chi141Slice.chiAD.value) = true := by
  norm_num [chi141Slice, chi141LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi141ValidityFacts :
    ChiFacts chi141Slice chi141LogChiCertificate :=
  { domain := by norm_num [chi141Slice]
    onePlusPositive := by
      norm_num [chi141Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi141LogChi_valid }

noncomputable def chi141InputQChi : RationalEnclosure :=
  { lower := (-1341817/16777216), upper := (-1004155/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi141InputQChi_eq :
    chi141InputQChi = outerEnclosure 24 chi141QChiValue := by
  rfl'

theorem chi141RoundedFacts :
    ChiRoundedFacts 8 chi141Slice chi141LogChiCertificate
      chi141InputQChi :=
  { coversQChi := by
      rw [chi141InputQChi_eq, chi141QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi142Slice : ChiSlice :=
  { lo := (5/256), hi := (3/128) }

noncomputable def chi142LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -6, mantissa := (5/4) }, upper := { exponent := -6, mantissa := (3/2) } }

private noncomputable def chi142QChiValue : RationalEnclosure :=
  { lower := (-24334326661326466663/268956615310900461945), upper := (-1050600612269401117593381102024527/14746086749049090617241210937500000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi142QChiValue_eq :
    chi142QChiValue =
      (chi142Slice.qChiAD 8 chi142LogChiCertificate).value := by
  norm_num [chi142QChiValue, chi142LogChiCertificate, chi142Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi142LogChi_valid :
    (if chi142Slice.lo = 0 then
      if chi142Slice.hi = 0 then true
      else decide (chi142Slice.hi ≤ 1 / 4) &&
        chi142LogChiCertificate.check
          (IntervalAD.const chi142Slice.hi).value
    else chi142LogChiCertificate.check
      chi142Slice.chiAD.value) = true := by
  norm_num [chi142Slice, chi142LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi142ValidityFacts :
    ChiFacts chi142Slice chi142LogChiCertificate :=
  { domain := by norm_num [chi142Slice]
    onePlusPositive := by
      norm_num [chi142Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi142LogChi_valid }

noncomputable def chi142InputQChi : RationalEnclosure :=
  { lower := (-1517949/16777216), upper := (-597655/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi142InputQChi_eq :
    chi142InputQChi = outerEnclosure 24 chi142QChiValue := by
  rfl'

theorem chi142RoundedFacts :
    ChiRoundedFacts 8 chi142Slice chi142LogChiCertificate
      chi142InputQChi :=
  { coversQChi := by
      rw [chi142InputQChi_eq, chi142QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi143Slice : ChiSlice :=
  { lo := (5/128), hi := (11/256) }

noncomputable def chi143LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (5/4) }, upper := { exponent := -5, mantissa := (11/8) } }

private noncomputable def chi143QChiValue : RationalEnclosure :=
  { lower := (-5728188412204250039/42718292086997774520), upper := (-1195299261249210407802244593021244469104601/10158289127678343078226908762363152465742720) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi143QChiValue_eq :
    chi143QChiValue =
      (chi143Slice.qChiAD 8 chi143LogChiCertificate).value := by
  norm_num [chi143QChiValue, chi143LogChiCertificate, chi143Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi143LogChi_valid :
    (if chi143Slice.lo = 0 then
      if chi143Slice.hi = 0 then true
      else decide (chi143Slice.hi ≤ 1 / 4) &&
        chi143LogChiCertificate.check
          (IntervalAD.const chi143Slice.hi).value
    else chi143LogChiCertificate.check
      chi143Slice.chiAD.value) = true := by
  norm_num [chi143Slice, chi143LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi143ValidityFacts :
    ChiFacts chi143Slice chi143LogChiCertificate :=
  { domain := by norm_num [chi143Slice]
    onePlusPositive := by
      norm_num [chi143Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi143LogChi_valid }

noncomputable def chi143InputQChi : RationalEnclosure :=
  { lower := (-1124847/8388608), upper := (-1974131/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi143InputQChi_eq :
    chi143InputQChi = outerEnclosure 24 chi143QChiValue := by
  rfl'

theorem chi143RoundedFacts :
    ChiRoundedFacts 8 chi143Slice chi143LogChiCertificate
      chi143InputQChi :=
  { coversQChi := by
      rw [chi143InputQChi_eq, chi143QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi144Slice : ChiSlice :=
  { lo := (11/256), hi := (3/64) }

noncomputable def chi144LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (11/8) }, upper := { exponent := -5, mantissa := (3/2) } }

private noncomputable def chi144QChiValue : RationalEnclosure :=
  { lower := (-462651366498676722172167393721/3270756187301498432078179532895), upper := (-358310913972334432590454367506925805855011497/2856960812238110617746413753122981201171875000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi144QChiValue_eq :
    chi144QChiValue =
      (chi144Slice.qChiAD 8 chi144LogChiCertificate).value := by
  norm_num [chi144QChiValue, chi144LogChiCertificate, chi144Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi144LogChi_valid :
    (if chi144Slice.lo = 0 then
      if chi144Slice.hi = 0 then true
      else decide (chi144Slice.hi ≤ 1 / 4) &&
        chi144LogChiCertificate.check
          (IntervalAD.const chi144Slice.hi).value
    else chi144LogChiCertificate.check
      chi144Slice.chiAD.value) = true := by
  norm_num [chi144Slice, chi144LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi144ValidityFacts :
    ChiFacts chi144Slice chi144LogChiCertificate :=
  { domain := by norm_num [chi144Slice]
    onePlusPositive := by
      norm_num [chi144Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi144LogChi_valid }

noncomputable def chi144InputQChi : RationalEnclosure :=
  { lower := (-2373153/16777216), upper := (-131509/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi144InputQChi_eq :
    chi144InputQChi = outerEnclosure 24 chi144QChiValue := by
  rfl'

theorem chi144RoundedFacts :
    ChiRoundedFacts 8 chi144Slice chi144LogChiCertificate
      chi144InputQChi :=
  { coversQChi := by
      rw [chi144InputQChi_eq, chi144QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi145Slice : ChiSlice :=
  { lo := (7/128), hi := (15/256) }

noncomputable def chi145LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (7/4) }, upper := { exponent := -5, mantissa := (15/8) } }

private noncomputable def chi145QChiValue : RationalEnclosure :=
  { lower := (-951076199336696794150841819/5890799563628493531010953960), upper := (-2991461029886070186366288949482182104679643517827827/20431597031210788372630511131385984682326046132389760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi145QChiValue_eq :
    chi145QChiValue =
      (chi145Slice.qChiAD 8 chi145LogChiCertificate).value := by
  norm_num [chi145QChiValue, chi145LogChiCertificate, chi145Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi145LogChi_valid :
    (if chi145Slice.lo = 0 then
      if chi145Slice.hi = 0 then true
      else decide (chi145Slice.hi ≤ 1 / 4) &&
        chi145LogChiCertificate.check
          (IntervalAD.const chi145Slice.hi).value
    else chi145LogChiCertificate.check
      chi145Slice.chiAD.value) = true := by
  norm_num [chi145Slice, chi145LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi145ValidityFacts :
    ChiFacts chi145Slice chi145LogChiCertificate :=
  { domain := by norm_num [chi145Slice]
    onePlusPositive := by
      norm_num [chi145Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi145LogChi_valid }

noncomputable def chi145InputQChi : RationalEnclosure :=
  { lower := (-2708701/16777216), upper := (-1228205/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi145InputQChi_eq :
    chi145InputQChi = outerEnclosure 24 chi145QChiValue := by
  rfl'

theorem chi145RoundedFacts :
    ChiRoundedFacts 8 chi145Slice chi145LogChiCertificate
      chi145InputQChi :=
  { coversQChi := by
      rw [chi145InputQChi_eq, chi145QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi146Slice : ChiSlice :=
  { lo := (15/256), hi := (1/16) }

noncomputable def chi146LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (15/8) }, upper := { exponent := -4, mantissa := (1) } }

private noncomputable def chi146QChiValue : RationalEnclosure :=
  { lower := (-2607717292346213392777149051131092/15567934241044900260525871187981685), upper := (-449975368304055677700961369435453907/2945723905088148084078634409134621440) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi146QChiValue_eq :
    chi146QChiValue =
      (chi146Slice.qChiAD 8 chi146LogChiCertificate).value := by
  norm_num [chi146QChiValue, chi146LogChiCertificate, chi146Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi146LogChi_valid :
    (if chi146Slice.lo = 0 then
      if chi146Slice.hi = 0 then true
      else decide (chi146Slice.hi ≤ 1 / 4) &&
        chi146LogChiCertificate.check
          (IntervalAD.const chi146Slice.hi).value
    else chi146LogChiCertificate.check
      chi146Slice.chiAD.value) = true := by
  norm_num [chi146Slice, chi146LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi146ValidityFacts :
    ChiFacts chi146Slice chi146LogChiCertificate :=
  { domain := by norm_num [chi146Slice]
    onePlusPositive := by
      norm_num [chi146Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi146LogChi_valid }

noncomputable def chi146InputQChi : RationalEnclosure :=
  { lower := (-2810279/16777216), upper := (-2562811/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi146InputQChi_eq :
    chi146InputQChi = outerEnclosure 24 chi146QChiValue := by
  rfl'

theorem chi146RoundedFacts :
    ChiRoundedFacts 8 chi146Slice chi146LogChiCertificate
      chi146InputQChi :=
  { coversQChi := by
      rw [chi146InputQChi_eq, chi146QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi147Slice : ChiSlice :=
  { lo := (9/128), hi := (19/256) }

noncomputable def chi147LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (9/8) }, upper := { exponent := -4, mantissa := (19/16) } }

private noncomputable def chi147QChiValue : RationalEnclosure :=
  { lower := (-478576062584220673275516827221/2599651812923811596837820958794), upper := (-56842490405351972634231816078846916238337121531771548849041/334156097636834713975836352659618108001758928710937500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi147QChiValue_eq :
    chi147QChiValue =
      (chi147Slice.qChiAD 8 chi147LogChiCertificate).value := by
  norm_num [chi147QChiValue, chi147LogChiCertificate, chi147Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi147LogChi_valid :
    (if chi147Slice.lo = 0 then
      if chi147Slice.hi = 0 then true
      else decide (chi147Slice.hi ≤ 1 / 4) &&
        chi147LogChiCertificate.check
          (IntervalAD.const chi147Slice.hi).value
    else chi147LogChiCertificate.check
      chi147Slice.chiAD.value) = true := by
  norm_num [chi147Slice, chi147LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi147ValidityFacts :
    ChiFacts chi147Slice chi147LogChiCertificate :=
  { domain := by norm_num [chi147Slice]
    onePlusPositive := by
      norm_num [chi147Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi147LogChi_valid }

noncomputable def chi147InputQChi : RationalEnclosure :=
  { lower := (-1544279/8388608), upper := (-2853931/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi147InputQChi_eq :
    chi147InputQChi = outerEnclosure 24 chi147QChiValue := by
  rfl'

theorem chi147RoundedFacts :
    ChiRoundedFacts 8 chi147Slice chi147LogChiCertificate
      chi147InputQChi :=
  { coversQChi := by
      rw [chi147InputQChi_eq, chi147QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi148Slice : ChiSlice :=
  { lo := (19/256), hi := (5/64) }

noncomputable def chi148LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (19/16) }, upper := { exponent := -4, mantissa := (5/4) } }

private noncomputable def chi148QChiValue : RationalEnclosure :=
  { lower := (-46389903153504438367189563105072044/245261551966056052229628753662109375), upper := (-395029677491009308359173382823382312006211701/2252310527895427488147254803727050781250000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi148QChiValue_eq :
    chi148QChiValue =
      (chi148Slice.qChiAD 8 chi148LogChiCertificate).value := by
  norm_num [chi148QChiValue, chi148LogChiCertificate, chi148Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi148LogChi_valid :
    (if chi148Slice.lo = 0 then
      if chi148Slice.hi = 0 then true
      else decide (chi148Slice.hi ≤ 1 / 4) &&
        chi148LogChiCertificate.check
          (IntervalAD.const chi148Slice.hi).value
    else chi148LogChiCertificate.check
      chi148Slice.chiAD.value) = true := by
  norm_num [chi148Slice, chi148LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi148ValidityFacts :
    ChiFacts chi148Slice chi148LogChiCertificate :=
  { domain := by norm_num [chi148Slice]
    onePlusPositive := by
      norm_num [chi148Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi148LogChi_valid }

noncomputable def chi148InputQChi : RationalEnclosure :=
  { lower := (-3173321/16777216), upper := (-2942533/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi148InputQChi_eq :
    chi148InputQChi = outerEnclosure 24 chi148QChiValue := by
  rfl'

theorem chi148RoundedFacts :
    ChiRoundedFacts 8 chi148Slice chi148LogChiCertificate
      chi148InputQChi :=
  { coversQChi := by
      rw [chi148InputQChi_eq, chi148QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi149Slice : ChiSlice :=
  { lo := (13/128), hi := (27/256) }

noncomputable def chi149LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (13/8) }, upper := { exponent := -4, mantissa := (27/16) } }

private noncomputable def chi149QChiValue : RationalEnclosure :=
  { lower := (-334193699711630417379671/1526167010653394189150070), upper := (-326532556874773980669999609149544966722763726958654153/1580766814234269498158964737201959790414489122834563840) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi149QChiValue_eq :
    chi149QChiValue =
      (chi149Slice.qChiAD 8 chi149LogChiCertificate).value := by
  norm_num [chi149QChiValue, chi149LogChiCertificate, chi149Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi149LogChi_valid :
    (if chi149Slice.lo = 0 then
      if chi149Slice.hi = 0 then true
      else decide (chi149Slice.hi ≤ 1 / 4) &&
        chi149LogChiCertificate.check
          (IntervalAD.const chi149Slice.hi).value
    else chi149LogChiCertificate.check
      chi149Slice.chiAD.value) = true := by
  norm_num [chi149Slice, chi149LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi149ValidityFacts :
    ChiFacts chi149Slice chi149LogChiCertificate :=
  { domain := by norm_num [chi149Slice]
    onePlusPositive := by
      norm_num [chi149Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi149LogChi_valid }

noncomputable def chi149InputQChi : RationalEnclosure :=
  { lower := (-3673805/16777216), upper := (-3465601/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi149InputQChi_eq :
    chi149InputQChi = outerEnclosure 24 chi149QChiValue := by
  rfl'

theorem chi149RoundedFacts :
    ChiRoundedFacts 8 chi149Slice chi149LogChiCertificate
      chi149InputQChi :=
  { coversQChi := by
      rw [chi149InputQChi_eq, chi149QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi150Slice : ChiSlice :=
  { lo := (27/256), hi := (7/64) }

noncomputable def chi150LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (27/16) }, upper := { exponent := -4, mantissa := (7/4) } }

private noncomputable def chi150QChiValue : RationalEnclosure :=
  { lower := (-21762048686078118374319376208242108/97785160068218865920388782026203105), upper := (-1825913520105615817559527001431409751937073143736818123/8682256497975574138732444724884890242531169616887707520) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi150QChiValue_eq :
    chi150QChiValue =
      (chi150Slice.qChiAD 8 chi150LogChiCertificate).value := by
  norm_num [chi150QChiValue, chi150LogChiCertificate, chi150Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi150LogChi_valid :
    (if chi150Slice.lo = 0 then
      if chi150Slice.hi = 0 then true
      else decide (chi150Slice.hi ≤ 1 / 4) &&
        chi150LogChiCertificate.check
          (IntervalAD.const chi150Slice.hi).value
    else chi150LogChiCertificate.check
      chi150Slice.chiAD.value) = true := by
  norm_num [chi150Slice, chi150LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi150ValidityFacts :
    ChiFacts chi150Slice chi150LogChiCertificate :=
  { domain := by norm_num [chi150Slice]
    onePlusPositive := by
      norm_num [chi150Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi150LogChi_valid }

noncomputable def chi150InputQChi : RationalEnclosure :=
  { lower := (-3733763/16777216), upper := (-882079/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi150InputQChi_eq :
    chi150InputQChi = outerEnclosure 24 chi150QChiValue := by
  rfl'

theorem chi150RoundedFacts :
    ChiRoundedFacts 8 chi150Slice chi150LogChiCertificate
      chi150InputQChi :=
  { coversQChi := by
      rw [chi150InputQChi_eq, chi150QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi151Slice : ChiSlice :=
  { lo := (1/16), hi := (17/256) }

noncomputable def chi151LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (1) }, upper := { exponent := -4, mantissa := (17/16) } }

private noncomputable def chi151QChiValue : RationalEnclosure :=
  { lower := (-597351034279/3447181417680), upper := (-63618958984404185129729329689707/400606739972824569204511232501760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi151QChiValue_eq :
    chi151QChiValue =
      (chi151Slice.qChiAD 8 chi151LogChiCertificate).value := by
  norm_num [chi151QChiValue, chi151LogChiCertificate, chi151Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi151LogChi_valid :
    (if chi151Slice.lo = 0 then
      if chi151Slice.hi = 0 then true
      else decide (chi151Slice.hi ≤ 1 / 4) &&
        chi151LogChiCertificate.check
          (IntervalAD.const chi151Slice.hi).value
    else chi151LogChiCertificate.check
      chi151Slice.chiAD.value) = true := by
  norm_num [chi151Slice, chi151LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi151ValidityFacts :
    ChiFacts chi151Slice chi151LogChiCertificate :=
  { domain := by norm_num [chi151Slice]
    onePlusPositive := by
      norm_num [chi151Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi151LogChi_valid }

noncomputable def chi151InputQChi : RationalEnclosure :=
  { lower := (-2907271/16777216), upper := (-2664331/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi151InputQChi_eq :
    chi151InputQChi = outerEnclosure 24 chi151QChiValue := by
  rfl'

theorem chi151RoundedFacts :
    ChiRoundedFacts 8 chi151Slice chi151LogChiCertificate
      chi151InputQChi :=
  { coversQChi := by
      rw [chi151InputQChi_eq, chi151QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi152Slice : ChiSlice :=
  { lo := (17/256), hi := (9/128) }

noncomputable def chi152LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (17/16) }, upper := { exponent := -4, mantissa := (9/8) } }

private noncomputable def chi152QChiValue : RationalEnclosure :=
  { lower := (-443767703501415479439519166/2481772038380522737601837085), upper := (-5591719008766256991630634266901991233568100662171/33974636135621197459083551396657982449950723251840) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi152QChiValue_eq :
    chi152QChiValue =
      (chi152Slice.qChiAD 8 chi152LogChiCertificate).value := by
  norm_num [chi152QChiValue, chi152LogChiCertificate, chi152Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi152LogChi_valid :
    (if chi152Slice.lo = 0 then
      if chi152Slice.hi = 0 then true
      else decide (chi152Slice.hi ≤ 1 / 4) &&
        chi152LogChiCertificate.check
          (IntervalAD.const chi152Slice.hi).value
    else chi152LogChiCertificate.check
      chi152Slice.chiAD.value) = true := by
  norm_num [chi152Slice, chi152LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi152ValidityFacts :
    ChiFacts chi152Slice chi152LogChiCertificate :=
  { domain := by norm_num [chi152Slice]
    onePlusPositive := by
      norm_num [chi152Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi152LogChi_valid }

noncomputable def chi152InputQChi : RationalEnclosure :=
  { lower := (-749987/4194304), upper := (-2761279/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi152InputQChi_eq :
    chi152InputQChi = outerEnclosure 24 chi152QChiValue := by
  rfl'

theorem chi152RoundedFacts :
    ChiRoundedFacts 8 chi152Slice chi152LogChiCertificate
      chi152InputQChi :=
  { coversQChi := by
      rw [chi152InputQChi_eq, chi152QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi153Slice : ChiSlice :=
  { lo := (15/128), hi := (31/256) }

noncomputable def chi153LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (15/8) }, upper := { exponent := -4, mantissa := (31/16) } }

private noncomputable def chi153QChiValue : RationalEnclosure :=
  { lower := (-763614458580345531971540681311651/3285925603644901457203246612371042), upper := (-49792708199435088575549218430135867982586951804648085670685127939/225709147256341469365880343580568263006308235019231157276173556480) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi153QChiValue_eq :
    chi153QChiValue =
      (chi153Slice.qChiAD 8 chi153LogChiCertificate).value := by
  norm_num [chi153QChiValue, chi153LogChiCertificate, chi153Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi153LogChi_valid :
    (if chi153Slice.lo = 0 then
      if chi153Slice.hi = 0 then true
      else decide (chi153Slice.hi ≤ 1 / 4) &&
        chi153LogChiCertificate.check
          (IntervalAD.const chi153Slice.hi).value
    else chi153LogChiCertificate.check
      chi153Slice.chiAD.value) = true := by
  norm_num [chi153Slice, chi153LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi153ValidityFacts :
    ChiFacts chi153Slice chi153LogChiCertificate :=
  { domain := by norm_num [chi153Slice]
    onePlusPositive := by
      norm_num [chi153Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi153LogChi_valid }

noncomputable def chi153InputQChi : RationalEnclosure :=
  { lower := (-3898849/16777216), upper := (-925287/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi153InputQChi_eq :
    chi153InputQChi = outerEnclosure 24 chi153QChiValue := by
  rfl'

theorem chi153RoundedFacts :
    ChiRoundedFacts 8 chi153Slice chi153LogChiCertificate
      chi153InputQChi :=
  { coversQChi := by
      rw [chi153InputQChi_eq, chi153QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi154Slice : ChiSlice :=
  { lo := (31/256), hi := (1/8) }

noncomputable def chi154LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (31/16) }, upper := { exponent := -3, mantissa := (1) } }

private noncomputable def chi154QChiValue : RationalEnclosure :=
  { lower := (-1227872719079593712838948511227669728/5216243849421005979963423519987343635), upper := (-21363692810017859669040493112569499211713/95478127419802093457250504109848337895040) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi154QChiValue_eq :
    chi154QChiValue =
      (chi154Slice.qChiAD 8 chi154LogChiCertificate).value := by
  norm_num [chi154QChiValue, chi154LogChiCertificate, chi154Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi154LogChi_valid :
    (if chi154Slice.lo = 0 then
      if chi154Slice.hi = 0 then true
      else decide (chi154Slice.hi ≤ 1 / 4) &&
        chi154LogChiCertificate.check
          (IntervalAD.const chi154Slice.hi).value
    else chi154LogChiCertificate.check
      chi154Slice.chiAD.value) = true := by
  norm_num [chi154Slice, chi154LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi154ValidityFacts :
    ChiFacts chi154Slice chi154LogChiCertificate :=
  { domain := by norm_num [chi154Slice]
    onePlusPositive := by
      norm_num [chi154Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi154LogChi_valid }

noncomputable def chi154InputQChi : RationalEnclosure :=
  { lower := (-3949257/16777216), upper := (-3753983/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi154InputQChi_eq :
    chi154InputQChi = outerEnclosure 24 chi154QChiValue := by
  rfl'

theorem chi154RoundedFacts :
    ChiRoundedFacts 8 chi154Slice chi154LogChiCertificate
      chi154InputQChi :=
  { coversQChi := by
      rw [chi154InputQChi_eq, chi154QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi155Slice : ChiSlice :=
  { lo := (7/64), hi := (29/256) }

noncomputable def chi155LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (7/4) }, upper := { exponent := -4, mantissa := (29/16) } }

private noncomputable def chi155QChiValue : RationalEnclosure :=
  { lower := (-150019536149111571218841313/663883760345433397939329732), upper := (-3671947177097913904476264591343245554786738134607/17167784856262456280630886854234673046875000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi155QChiValue_eq :
    chi155QChiValue =
      (chi155Slice.qChiAD 8 chi155LogChiCertificate).value := by
  norm_num [chi155QChiValue, chi155LogChiCertificate, chi155Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi155LogChi_valid :
    (if chi155Slice.lo = 0 then
      if chi155Slice.hi = 0 then true
      else decide (chi155Slice.hi ≤ 1 / 4) &&
        chi155LogChiCertificate.check
          (IntervalAD.const chi155Slice.hi).value
    else chi155LogChiCertificate.check
      chi155Slice.chiAD.value) = true := by
  norm_num [chi155Slice, chi155LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi155ValidityFacts :
    ChiFacts chi155Slice chi155LogChiCertificate :=
  { domain := by norm_num [chi155Slice]
    onePlusPositive := by
      norm_num [chi155Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi155LogChi_valid }

noncomputable def chi155InputQChi : RationalEnclosure :=
  { lower := (-473899/2097152), upper := (-1794205/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi155InputQChi_eq :
    chi155InputQChi = outerEnclosure 24 chi155QChiValue := by
  rfl'

theorem chi155RoundedFacts :
    ChiRoundedFacts 8 chi155Slice chi155LogChiCertificate
      chi155InputQChi :=
  { coversQChi := by
      rw [chi155InputQChi_eq, chi155QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi156Slice : ChiSlice :=
  { lo := (29/256), hi := (15/128) }

noncomputable def chi156LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (29/16) }, upper := { exponent := -4, mantissa := (15/8) } }

private noncomputable def chi156QChiValue : RationalEnclosure :=
  { lower := (-410938962922041582902709248722/1792530872180845335845947265625), upper := (-28517850138175511852191739425473125282191447699652573933/131226471242691136030942888043051585723259667968750000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi156QChiValue_eq :
    chi156QChiValue =
      (chi156Slice.qChiAD 8 chi156LogChiCertificate).value := by
  norm_num [chi156QChiValue, chi156LogChiCertificate, chi156Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi156LogChi_valid :
    (if chi156Slice.lo = 0 then
      if chi156Slice.hi = 0 then true
      else decide (chi156Slice.hi ≤ 1 / 4) &&
        chi156LogChiCertificate.check
          (IntervalAD.const chi156Slice.hi).value
    else chi156LogChiCertificate.check
      chi156Slice.chiAD.value) = true := by
  norm_num [chi156Slice, chi156LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi156ValidityFacts :
    ChiFacts chi156Slice chi156LogChiCertificate :=
  { domain := by norm_num [chi156Slice]
    onePlusPositive := by
      norm_num [chi156Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi156LogChi_valid }

noncomputable def chi156InputQChi : RationalEnclosure :=
  { lower := (-3846189/16777216), upper := (-3645987/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi156InputQChi_eq :
    chi156InputQChi = outerEnclosure 24 chi156QChiValue := by
  rfl'

theorem chi156RoundedFacts :
    ChiRoundedFacts 8 chi156Slice chi156LogChiCertificate
      chi156InputQChi :=
  { coversQChi := by
      rw [chi156InputQChi_eq, chi156QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi157Slice : ChiSlice :=
  { lo := (1/128), hi := (3/256) }

noncomputable def chi157LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -7, mantissa := (1) }, upper := { exponent := -7, mantissa := (3/2) } }

private noncomputable def chi157QChiValue : RationalEnclosure :=
  { lower := (-597351034279/10587771497160), upper := (-1812014844514556787616853/54074227363519042968750000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi157QChiValue_eq :
    chi157QChiValue =
      (chi157Slice.qChiAD 8 chi157LogChiCertificate).value := by
  norm_num [chi157QChiValue, chi157LogChiCertificate, chi157Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi157LogChi_valid :
    (if chi157Slice.lo = 0 then
      if chi157Slice.hi = 0 then true
      else decide (chi157Slice.hi ≤ 1 / 4) &&
        chi157LogChiCertificate.check
          (IntervalAD.const chi157Slice.hi).value
    else chi157LogChiCertificate.check
      chi157Slice.chiAD.value) = true := by
  norm_num [chi157Slice, chi157LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi157ValidityFacts :
    ChiFacts chi157Slice chi157LogChiCertificate :=
  { domain := by norm_num [chi157Slice]
    onePlusPositive := by
      norm_num [chi157Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi157LogChi_valid }

noncomputable def chi157InputQChi : RationalEnclosure :=
  { lower := (-473277/8388608), upper := (-70275/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi157InputQChi_eq :
    chi157InputQChi = outerEnclosure 24 chi157QChiValue := by
  rfl'

theorem chi157RoundedFacts :
    ChiRoundedFacts 8 chi157Slice chi157LogChiCertificate
      chi157InputQChi :=
  { coversQChi := by
      rw [chi157InputQChi_eq, chi157QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi158Slice : ChiSlice :=
  { lo := (3/256), hi := (1/64) }

noncomputable def chi158LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -7, mantissa := (3/2) }, upper := { exponent := -6, mantissa := (1) } }

private noncomputable def chi158QChiValue : RationalEnclosure :=
  { lower := (-116944253338809774363869/1702918981893768310546875), upper := (-335741518563587873910241037/7084142964678076171875000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi158QChiValue_eq :
    chi158QChiValue =
      (chi158Slice.qChiAD 8 chi158LogChiCertificate).value := by
  norm_num [chi158QChiValue, chi158LogChiCertificate, chi158Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi158LogChi_valid :
    (if chi158Slice.lo = 0 then
      if chi158Slice.hi = 0 then true
      else decide (chi158Slice.hi ≤ 1 / 4) &&
        chi158LogChiCertificate.check
          (IntervalAD.const chi158Slice.hi).value
    else chi158LogChiCertificate.check
      chi158Slice.chiAD.value) = true := by
  norm_num [chi158Slice, chi158LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi158ValidityFacts :
    ChiFacts chi158Slice chi158LogChiCertificate :=
  { domain := by norm_num [chi158Slice]
    onePlusPositive := by
      norm_num [chi158Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi158LogChi_valid }

noncomputable def chi158InputQChi : RationalEnclosure :=
  { lower := (-1152139/16777216), upper := (-795129/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi158InputQChi_eq :
    chi158InputQChi = outerEnclosure 24 chi158QChiValue := by
  rfl'

theorem chi158RoundedFacts :
    ChiRoundedFacts 8 chi158Slice chi158LogChiCertificate
      chi158InputQChi :=
  { coversQChi := by
      rw [chi158InputQChi_eq, chi158QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi159Slice : ChiSlice :=
  { lo := (3/64), hi := (13/256) }

noncomputable def chi159LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (3/2) }, upper := { exponent := -5, mantissa := (13/8) } }

private noncomputable def chi159QChiValue : RationalEnclosure :=
  { lower := (-7316803602317445751829/49289336301269531250000), upper := (-390243664197088422854614320889701097009/2939245016824837471973135976562500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi159QChiValue_eq :
    chi159QChiValue =
      (chi159Slice.qChiAD 8 chi159LogChiCertificate).value := by
  norm_num [chi159QChiValue, chi159LogChiCertificate, chi159Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi159LogChi_valid :
    (if chi159Slice.lo = 0 then
      if chi159Slice.hi = 0 then true
      else decide (chi159Slice.hi ≤ 1 / 4) &&
        chi159LogChiCertificate.check
          (IntervalAD.const chi159Slice.hi).value
    else chi159LogChiCertificate.check
      chi159Slice.chiAD.value) = true := by
  norm_num [chi159Slice, chi159LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi159ValidityFacts :
    ChiFacts chi159Slice chi159LogChiCertificate :=
  { domain := by norm_num [chi159Slice]
    onePlusPositive := by
      norm_num [chi159Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi159LogChi_valid }

noncomputable def chi159InputQChi : RationalEnclosure :=
  { lower := (-2490511/16777216), upper := (-2227511/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi159InputQChi_eq :
    chi159InputQChi = outerEnclosure 24 chi159QChiValue := by
  rfl'

theorem chi159RoundedFacts :
    ChiRoundedFacts 8 chi159Slice chi159LogChiCertificate
      chi159InputQChi :=
  { coversQChi := by
      rw [chi159InputQChi_eq, chi159QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi160Slice : ChiSlice :=
  { lo := (13/256), hi := (7/128) }

noncomputable def chi160LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -5, mantissa := (13/8) }, upper := { exponent := -5, mantissa := (7/4) } }

private noncomputable def chi160QChiValue : RationalEnclosure :=
  { lower := (-116127470192316892180637/748703208265829246592162), upper := (-8669772071278084569164486636094370171669/62033436816477225576449422739041125172800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi160QChiValue_eq :
    chi160QChiValue =
      (chi160Slice.qChiAD 8 chi160LogChiCertificate).value := by
  norm_num [chi160QChiValue, chi160LogChiCertificate, chi160Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi160LogChi_valid :
    (if chi160Slice.lo = 0 then
      if chi160Slice.hi = 0 then true
      else decide (chi160Slice.hi ≤ 1 / 4) &&
        chi160LogChiCertificate.check
          (IntervalAD.const chi160Slice.hi).value
    else chi160LogChiCertificate.check
      chi160Slice.chiAD.value) = true := by
  norm_num [chi160Slice, chi160LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi160ValidityFacts :
    ChiFacts chi160Slice chi160LogChiCertificate :=
  { domain := by norm_num [chi160Slice]
    onePlusPositive := by
      norm_num [chi160Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi160LogChi_valid }

noncomputable def chi160InputQChi : RationalEnclosure :=
  { lower := (-2602227/16777216), upper := (-1172389/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi160InputQChi_eq :
    chi160InputQChi = outerEnclosure 24 chi160QChiValue := by
  rfl'

theorem chi160RoundedFacts :
    ChiRoundedFacts 8 chi160Slice chi160LogChiCertificate
      chi160InputQChi :=
  { coversQChi := by
      rw [chi160InputQChi_eq, chi160QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi161Slice : ChiSlice :=
  { lo := (1/16), hi := (33/512) }

noncomputable def chi161LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (1) }, upper := { exponent := -4, mantissa := (33/32) } }

private noncomputable def chi161QChiValue : RationalEnclosure :=
  { lower := (-597351034279/3551641460640), upper := (-147437461029487009176150393419424237620479/916029005239060625182015541250000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi161QChiValue_eq :
    chi161QChiValue =
      (chi161Slice.qChiAD 8 chi161LogChiCertificate).value := by
  norm_num [chi161QChiValue, chi161LogChiCertificate, chi161Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi161LogChi_valid :
    (if chi161Slice.lo = 0 then
      if chi161Slice.hi = 0 then true
      else decide (chi161Slice.hi ≤ 1 / 4) &&
        chi161LogChiCertificate.check
          (IntervalAD.const chi161Slice.hi).value
    else chi161LogChiCertificate.check
      chi161Slice.chiAD.value) = true := by
  norm_num [chi161Slice, chi161LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi161ValidityFacts :
    ChiFacts chi161Slice chi161LogChiCertificate :=
  { domain := by norm_num [chi161Slice]
    onePlusPositive := by
      norm_num [chi161Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi161LogChi_valid }

noncomputable def chi161InputQChi : RationalEnclosure :=
  { lower := (-2821763/16777216), upper := (-675085/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi161InputQChi_eq :
    chi161InputQChi = outerEnclosure 24 chi161QChiValue := by
  rfl'

theorem chi161RoundedFacts :
    ChiRoundedFacts 8 chi161Slice chi161LogChiCertificate
      chi161InputQChi :=
  { coversQChi := by
      rw [chi161InputQChi_eq, chi161QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi162Slice : ChiSlice :=
  { lo := (33/512), hi := (17/256) }

noncomputable def chi162LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (33/32) }, upper := { exponent := -4, mantissa := (17/16) } }

private noncomputable def chi162QChiValue : RationalEnclosure :=
  { lower := (-2413340254702036271889743700637008788198/14109046244814058486151649643707275390625), upper := (-347729597878079723891533729929478689979785382638930947476261/2121903006595442031029952825333605567138700345117187500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi162QChiValue_eq :
    chi162QChiValue =
      (chi162Slice.qChiAD 8 chi162LogChiCertificate).value := by
  norm_num [chi162QChiValue, chi162LogChiCertificate, chi162Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi162LogChi_valid :
    (if chi162Slice.lo = 0 then
      if chi162Slice.hi = 0 then true
      else decide (chi162Slice.hi ≤ 1 / 4) &&
        chi162LogChiCertificate.check
          (IntervalAD.const chi162Slice.hi).value
    else chi162LogChiCertificate.check
      chi162Slice.chiAD.value) = true := by
  norm_num [chi162Slice, chi162LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi162ValidityFacts :
    ChiFacts chi162Slice chi162LogChiCertificate :=
  { domain := by norm_num [chi162Slice]
    onePlusPositive := by
      norm_num [chi162Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi162LogChi_valid }

noncomputable def chi162InputQChi : RationalEnclosure :=
  { lower := (-2869729/16777216), upper := (-2749387/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi162InputQChi_eq :
    chi162InputQChi = outerEnclosure 24 chi162QChiValue := by
  rfl'

theorem chi162RoundedFacts :
    ChiRoundedFacts 8 chi162Slice chi162LogChiCertificate
      chi162InputQChi :=
  { coversQChi := by
      rw [chi162InputQChi_eq, chi162QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi163Slice : ChiSlice :=
  { lo := (17/256), hi := (35/512) }

noncomputable def chi163LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (17/16) }, upper := { exponent := -4, mantissa := (35/32) } }

private noncomputable def chi163QChiValue : RationalEnclosure :=
  { lower := (-221883851750707739719759583/1276339905452840265052373358), upper := (-2566888462591666165289462925738766025387435111722901362011059/15395142898715836846843239481887134757535101949041079647521280) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi163QChiValue_eq :
    chi163QChiValue =
      (chi163Slice.qChiAD 8 chi163LogChiCertificate).value := by
  norm_num [chi163QChiValue, chi163LogChiCertificate, chi163Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi163LogChi_valid :
    (if chi163Slice.lo = 0 then
      if chi163Slice.hi = 0 then true
      else decide (chi163Slice.hi ≤ 1 / 4) &&
        chi163LogChiCertificate.check
          (IntervalAD.const chi163Slice.hi).value
    else chi163LogChiCertificate.check
      chi163Slice.chiAD.value) = true := by
  norm_num [chi163Slice, chi163LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi163ValidityFacts :
    ChiFacts chi163Slice chi163LogChiCertificate :=
  { domain := by norm_num [chi163Slice]
    onePlusPositive := by
      norm_num [chi163Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi163LogChi_valid }

noncomputable def chi163InputQChi : RationalEnclosure :=
  { lower := (-364577/2097152), upper := (-1398663/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi163InputQChi_eq :
    chi163InputQChi = outerEnclosure 24 chi163QChiValue := by
  rfl'

theorem chi163RoundedFacts :
    ChiRoundedFacts 8 chi163Slice chi163LogChiCertificate
      chi163InputQChi :=
  { coversQChi := by
      rw [chi163InputQChi_eq, chi163QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi164Slice : ChiSlice :=
  { lo := (35/512), hi := (9/128) }

noncomputable def chi164LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (35/32) }, upper := { exponent := -4, mantissa := (9/8) } }

private noncomputable def chi164QChiValue : RationalEnclosure :=
  { lower := (-162582963134755094278244495753755401788/920752634996080315488005697292400980407), upper := (-29915934930080488354515394647875418365523630968263500122086357/176467174928150245538751885830481768886370324953722980692238592) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi164QChiValue_eq :
    chi164QChiValue =
      (chi164Slice.qChiAD 8 chi164LogChiCertificate).value := by
  norm_num [chi164QChiValue, chi164LogChiCertificate, chi164Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi164LogChi_valid :
    (if chi164Slice.lo = 0 then
      if chi164Slice.hi = 0 then true
      else decide (chi164Slice.hi ≤ 1 / 4) &&
        chi164LogChiCertificate.check
          (IntervalAD.const chi164Slice.hi).value
    else chi164LogChiCertificate.check
      chi164Slice.chiAD.value) = true := by
  norm_num [chi164Slice, chi164LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi164ValidityFacts :
    ChiFacts chi164Slice chi164LogChiCertificate :=
  { domain := by norm_num [chi164Slice]
    onePlusPositive := by
      norm_num [chi164Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi164LogChi_valid }

noncomputable def chi164InputQChi : RationalEnclosure :=
  { lower := (-2962457/16777216), upper := (-2844189/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi164InputQChi_eq :
    chi164InputQChi = outerEnclosure 24 chi164QChiValue := by
  rfl'

theorem chi164RoundedFacts :
    ChiRoundedFacts 8 chi164Slice chi164LogChiCertificate
      chi164InputQChi :=
  { coversQChi := by
      rw [chi164InputQChi_eq, chi164QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi165Slice : ChiSlice :=
  { lo := (27/256), hi := (55/512) }

noncomputable def chi165LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (27/16) }, upper := { exponent := -4, mantissa := (55/32) } }

private noncomputable def chi165QChiValue : RationalEnclosure :=
  { lower := (-5440512171519529593579844052060527/24890768017364802234280780879397154), upper := (-9372445211482662859082553380645591271568232887843880336133254921/44115146901112516847306931778941765876158318245717419082529671680) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi165QChiValue_eq :
    chi165QChiValue =
      (chi165Slice.qChiAD 8 chi165LogChiCertificate).value := by
  norm_num [chi165QChiValue, chi165LogChiCertificate, chi165Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi165LogChi_valid :
    (if chi165Slice.lo = 0 then
      if chi165Slice.hi = 0 then true
      else decide (chi165Slice.hi ≤ 1 / 4) &&
        chi165LogChiCertificate.check
          (IntervalAD.const chi165Slice.hi).value
    else chi165LogChiCertificate.check
      chi165Slice.chiAD.value) = true := by
  norm_num [chi165Slice, chi165LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi165ValidityFacts :
    ChiFacts chi165Slice chi165LogChiCertificate :=
  { domain := by norm_num [chi165Slice]
    onePlusPositive := by
      norm_num [chi165Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi165LogChi_valid }

noncomputable def chi165InputQChi : RationalEnclosure :=
  { lower := (-3667089/16777216), upper := (-891097/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi165InputQChi_eq :
    chi165InputQChi = outerEnclosure 24 chi165QChiValue := by
  rfl'

theorem chi165RoundedFacts :
    ChiRoundedFacts 8 chi165Slice chi165LogChiCertificate
      chi165InputQChi :=
  { coversQChi := by
      rw [chi165InputQChi_eq, chi165QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi166Slice : ChiSlice :=
  { lo := (55/512), hi := (7/64) }

noncomputable def chi166LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (55/32) }, upper := { exponent := -4, mantissa := (7/4) } }

private noncomputable def chi166QChiValue : RationalEnclosure :=
  { lower := (-2212130636381632139561827753025512/10039402946376161933448833571795183), upper := (-1194622579997119730562169176132172212150828385162433/5575484069623875946042846956593554425125697218404608) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi166QChiValue_eq :
    chi166QChiValue =
      (chi166Slice.qChiAD 8 chi166LogChiCertificate).value := by
  norm_num [chi166QChiValue, chi166LogChiCertificate, chi166Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi166LogChi_valid :
    (if chi166Slice.lo = 0 then
      if chi166Slice.hi = 0 then true
      else decide (chi166Slice.hi ≤ 1 / 4) &&
        chi166LogChiCertificate.check
          (IntervalAD.const chi166Slice.hi).value
    else chi166LogChiCertificate.check
      chi166Slice.chiAD.value) = true := by
  norm_num [chi166Slice, chi166LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi166ValidityFacts :
    ChiFacts chi166Slice chi166LogChiCertificate :=
  { domain := by norm_num [chi166Slice]
    onePlusPositive := by
      norm_num [chi166Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi166LogChi_valid }

noncomputable def chi166InputQChi : RationalEnclosure :=
  { lower := (-3696773/16777216), upper := (-449343/2097152) }

set_option maxRecDepth 1000000 in
private theorem chi166InputQChi_eq :
    chi166InputQChi = outerEnclosure 24 chi166QChiValue := by
  rfl'

theorem chi166RoundedFacts :
    ChiRoundedFacts 8 chi166Slice chi166LogChiCertificate
      chi166InputQChi :=
  { coversQChi := by
      rw [chi166InputQChi_eq, chi166QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi167Slice : ChiSlice :=
  { lo := (29/256), hi := (59/512) }

noncomputable def chi167LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (29/16) }, upper := { exponent := -4, mantissa := (59/32) } }

private noncomputable def chi167QChiValue : RationalEnclosure :=
  { lower := (-12122699406200226695629922837299/53775926165425360075378417968750), upper := (-426698034227960499183443351078404827645403435324773489899790553/1944267623321929047047365169858612988878618695290234375000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi167QChiValue_eq :
    chi167QChiValue =
      (chi167Slice.qChiAD 8 chi167LogChiCertificate).value := by
  norm_num [chi167QChiValue, chi167LogChiCertificate, chi167Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi167LogChi_valid :
    (if chi167Slice.lo = 0 then
      if chi167Slice.hi = 0 then true
      else decide (chi167Slice.hi ≤ 1 / 4) &&
        chi167LogChiCertificate.check
          (IntervalAD.const chi167Slice.hi).value
    else chi167LogChiCertificate.check
      chi167Slice.chiAD.value) = true := by
  norm_num [chi167Slice, chi167LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi167ValidityFacts :
    ChiFacts chi167Slice chi167LogChiCertificate :=
  { domain := by norm_num [chi167Slice]
    onePlusPositive := by
      norm_num [chi167Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi167LogChi_valid }

noncomputable def chi167InputQChi : RationalEnclosure :=
  { lower := (-1891043/8388608), upper := (-1841003/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi167InputQChi_eq :
    chi167InputQChi = outerEnclosure 24 chi167QChiValue := by
  rfl'

theorem chi167RoundedFacts :
    ChiRoundedFacts 8 chi167Slice chi167LogChiCertificate
      chi167InputQChi :=
  { coversQChi := by
      rw [chi167InputQChi_eq, chi167QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi168Slice : ChiSlice :=
  { lo := (59/512), hi := (15/128) }

noncomputable def chi168LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (59/32) }, upper := { exponent := -4, mantissa := (15/8) } }

private noncomputable def chi168QChiValue : RationalEnclosure :=
  { lower := (-4972738813726891799718648608094315512572/21901229645903943614739697844051081453817), upper := (-236358058435377786730501258923088898510948488268097586281267806593/1068887618398884464061784845882370903437649174831864972380626453760) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi168QChiValue_eq :
    chi168QChiValue =
      (chi168Slice.qChiAD 8 chi168LogChiCertificate).value := by
  norm_num [chi168QChiValue, chi168LogChiCertificate, chi168Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi168LogChi_valid :
    (if chi168Slice.lo = 0 then
      if chi168Slice.hi = 0 then true
      else decide (chi168Slice.hi ≤ 1 / 4) &&
        chi168LogChiCertificate.check
          (IntervalAD.const chi168Slice.hi).value
    else chi168LogChiCertificate.check
      chi168Slice.chiAD.value) = true := by
  norm_num [chi168Slice, chi168LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi168ValidityFacts :
    ChiFacts chi168Slice chi168LogChiCertificate :=
  { domain := by norm_num [chi168Slice]
    onePlusPositive := by
      norm_num [chi168Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi168LogChi_valid }

noncomputable def chi168InputQChi : RationalEnclosure :=
  { lower := (-3809317/16777216), upper := (-1854933/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi168InputQChi_eq :
    chi168InputQChi = outerEnclosure 24 chi168QChiValue := by
  rfl'

theorem chi168RoundedFacts :
    ChiRoundedFacts 8 chi168Slice chi168LogChiCertificate
      chi168InputQChi :=
  { coversQChi := by
      rw [chi168InputQChi_eq, chi168QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi169Slice : ChiSlice :=
  { lo := (15/128), hi := (61/512) }

noncomputable def chi169LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (15/8) }, upper := { exponent := -4, mantissa := (61/32) } }

private noncomputable def chi169QChiValue : RationalEnclosure :=
  { lower := (-1502596192690357337105289727742281/6571851207289802914406493224742084), upper := (-102455427527593314608371365678361806179876424481731954610996109/459956009163109417921139489270207757374374772699410366747259904) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi169QChiValue_eq :
    chi169QChiValue =
      (chi169Slice.qChiAD 8 chi169LogChiCertificate).value := by
  norm_num [chi169QChiValue, chi169LogChiCertificate, chi169Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi169LogChi_valid :
    (if chi169Slice.lo = 0 then
      if chi169Slice.hi = 0 then true
      else decide (chi169Slice.hi ≤ 1 / 4) &&
        chi169LogChiCertificate.check
          (IntervalAD.const chi169Slice.hi).value
    else chi169LogChiCertificate.check
      chi169Slice.chiAD.value) = true := by
  norm_num [chi169Slice, chi169LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi169ValidityFacts :
    ChiFacts chi169Slice chi169LogChiCertificate :=
  { domain := by norm_num [chi169Slice]
    onePlusPositive := by
      norm_num [chi169Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi169LogChi_valid }

noncomputable def chi169InputQChi : RationalEnclosure :=
  { lower := (-958991/4194304), upper := (-3737133/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi169InputQChi_eq :
    chi169InputQChi = outerEnclosure 24 chi169QChiValue := by
  rfl'

theorem chi169RoundedFacts :
    ChiRoundedFacts 8 chi169Slice chi169LogChiCertificate
      chi169InputQChi :=
  { coversQChi := by
      rw [chi169InputQChi_eq, chi169QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi170Slice : ChiSlice :=
  { lo := (61/512), hi := (31/256) }

noncomputable def chi170LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (61/32) }, upper := { exponent := -4, mantissa := (31/16) } }

private noncomputable def chi170QChiValue : RationalEnclosure :=
  { lower := (-4302185051365231736361494355329738/18689276472535208398905389436786693), upper := (-453186594206525975001029255925223841190122104343615658438733459/2020079062516332297791174338722094412061640547838660686483063040) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi170QChiValue_eq :
    chi170QChiValue =
      (chi170Slice.qChiAD 8 chi170LogChiCertificate).value := by
  norm_num [chi170QChiValue, chi170LogChiCertificate, chi170Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi170LogChi_valid :
    (if chi170Slice.lo = 0 then
      if chi170Slice.hi = 0 then true
      else decide (chi170Slice.hi ≤ 1 / 4) &&
        chi170LogChiCertificate.check
          (IntervalAD.const chi170Slice.hi).value
    else chi170LogChiCertificate.check
      chi170Slice.chiAD.value) = true := by
  norm_num [chi170Slice, chi170LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi170ValidityFacts :
    ChiFacts chi170Slice chi170LogChiCertificate :=
  { domain := by norm_num [chi170Slice]
    onePlusPositive := by
      norm_num [chi170Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi170LogChi_valid }

noncomputable def chi170InputQChi : RationalEnclosure :=
  { lower := (-1931019/8388608), upper := (-3763817/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi170InputQChi_eq :
    chi170InputQChi = outerEnclosure 24 chi170QChiValue := by
  rfl'

theorem chi170RoundedFacts :
    ChiRoundedFacts 8 chi170Slice chi170LogChiCertificate
      chi170InputQChi :=
  { coversQChi := by
      rw [chi170InputQChi_eq, chi170QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi171Slice : ChiSlice :=
  { lo := (31/256), hi := (63/512) }

noncomputable def chi171LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (31/16) }, upper := { exponent := -4, mantissa := (63/32) } }

private noncomputable def chi171QChiValue : RationalEnclosure :=
  { lower := (-38371022471237303526217140975864679/165595042838762094602013445078963290), upper := (-8755237363418429228174826799758482772890263616664642460559786322229573/38757566454491625939689766703282560253429599744255161072765625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi171QChiValue_eq :
    chi171QChiValue =
      (chi171Slice.qChiAD 8 chi171LogChiCertificate).value := by
  norm_num [chi171QChiValue, chi171LogChiCertificate, chi171Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi171LogChi_valid :
    (if chi171Slice.lo = 0 then
      if chi171Slice.hi = 0 then true
      else decide (chi171Slice.hi ≤ 1 / 4) &&
        chi171LogChiCertificate.check
          (IntervalAD.const chi171Slice.hi).value
    else chi171LogChiCertificate.check
      chi171Slice.chiAD.value) = true := by
  norm_num [chi171Slice, chi171LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi171ValidityFacts :
    ChiFacts chi171Slice chi171LogChiCertificate :=
  { domain := by norm_num [chi171Slice]
    onePlusPositive := by
      norm_num [chi171Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi171LogChi_valid }

noncomputable def chi171InputQChi : RationalEnclosure :=
  { lower := (-1943775/8388608), upper := (-3789931/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi171InputQChi_eq :
    chi171InputQChi = outerEnclosure 24 chi171QChiValue := by
  rfl'

theorem chi171RoundedFacts :
    ChiRoundedFacts 8 chi171Slice chi171LogChiCertificate
      chi171InputQChi :=
  { coversQChi := by
      rw [chi171InputQChi_eq, chi171QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi172Slice : ChiSlice :=
  { lo := (63/512), hi := (1/8) }

noncomputable def chi172LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (63/32) }, upper := { exponent := -3, mantissa := (1) } }

private noncomputable def chi172QChiValue : RationalEnclosure :=
  { lower := (-1912069068520379104844995245560918749556672/8199135078205050216434819821666717529296875), upper := (-1307526421239604953280071908160169476518491247/5749376110490915212637424960166992187500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi172QChiValue_eq :
    chi172QChiValue =
      (chi172Slice.qChiAD 8 chi172LogChiCertificate).value := by
  norm_num [chi172QChiValue, chi172LogChiCertificate, chi172Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi172LogChi_valid :
    (if chi172Slice.lo = 0 then
      if chi172Slice.hi = 0 then true
      else decide (chi172Slice.hi ≤ 1 / 4) &&
        chi172LogChiCertificate.check
          (IntervalAD.const chi172Slice.hi).value
    else chi172LogChiCertificate.check
      chi172Slice.chiAD.value) = true := by
  norm_num [chi172Slice, chi172LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi172ValidityFacts :
    ChiFacts chi172Slice chi172LogChiCertificate :=
  { domain := by norm_num [chi172Slice]
    onePlusPositive := by
      norm_num [chi172Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi172LogChi_valid }

noncomputable def chi172InputQChi : RationalEnclosure :=
  { lower := (-1956255/8388608), upper := (-953871/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi172InputQChi_eq :
    chi172InputQChi = outerEnclosure 24 chi172QChiValue := by
  rfl'

theorem chi172RoundedFacts :
    ChiRoundedFacts 8 chi172Slice chi172LogChiCertificate
      chi172InputQChi :=
  { coversQChi := by
      rw [chi172InputQChi_eq, chi172QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi173Slice : ChiSlice :=
  { lo := (7/64), hi := (57/512) }

noncomputable def chi173LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (7/4) }, upper := { exponent := -4, mantissa := (57/32) } }

private noncomputable def chi173QChiValue : RationalEnclosure :=
  { lower := (-98288661614935167350275343/442589173563622265292886488), upper := (-1612678780704296188764116260292728946389578310623571793804806747/7464913210979031181774274153978516178816168948677084642927646720) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi173QChiValue_eq :
    chi173QChiValue =
      (chi173Slice.qChiAD 8 chi173LogChiCertificate).value := by
  norm_num [chi173QChiValue, chi173LogChiCertificate, chi173Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi173LogChi_valid :
    (if chi173Slice.lo = 0 then
      if chi173Slice.hi = 0 then true
      else decide (chi173Slice.hi ≤ 1 / 4) &&
        chi173LogChiCertificate.check
          (IntervalAD.const chi173Slice.hi).value
    else chi173LogChiCertificate.check
      chi173Slice.chiAD.value) = true := by
  norm_num [chi173Slice, chi173LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi173ValidityFacts :
    ChiFacts chi173Slice chi173LogChiCertificate :=
  { domain := by norm_num [chi173Slice]
    onePlusPositive := by
      norm_num [chi173Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi173LogChi_valid }

noncomputable def chi173InputQChi : RationalEnclosure :=
  { lower := (-1862913/8388608), upper := (-3624457/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi173InputQChi_eq :
    chi173InputQChi = outerEnclosure 24 chi173QChiValue := by
  rfl'

theorem chi173RoundedFacts :
    ChiRoundedFacts 8 chi173Slice chi173LogChiCertificate
      chi173InputQChi :=
  { coversQChi := by
      rw [chi173InputQChi_eq, chi173QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi174Slice : ChiSlice :=
  { lo := (57/512), hi := (29/256) }

noncomputable def chi174LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -4, mantissa := (57/32) }, upper := { exponent := -4, mantissa := (29/16) } }

private noncomputable def chi174QChiValue : RationalEnclosure :=
  { lower := (-4776511967545812081360723425115310964184518/21345509395701846381617664357090426031417005), upper := (-78305012543621367989468949799008485961296909116343133003167637299/359580012319155145728884712048632871854542132058752382812500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi174QChiValue_eq :
    chi174QChiValue =
      (chi174Slice.qChiAD 8 chi174LogChiCertificate).value := by
  norm_num [chi174QChiValue, chi174LogChiCertificate, chi174Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi174LogChi_valid :
    (if chi174Slice.lo = 0 then
      if chi174Slice.hi = 0 then true
      else decide (chi174Slice.hi ≤ 1 / 4) &&
        chi174LogChiCertificate.check
          (IntervalAD.const chi174Slice.hi).value
    else chi174LogChiCertificate.check
      chi174Slice.chiAD.value) = true := by
  norm_num [chi174Slice, chi174LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi174ValidityFacts :
    ChiFacts chi174Slice chi174LogChiCertificate :=
  { domain := by norm_num [chi174Slice]
    onePlusPositive := by
      norm_num [chi174Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi174LogChi_valid }

noncomputable def chi174InputQChi : RationalEnclosure :=
  { lower := (-938565/4194304), upper := (-913385/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi174InputQChi_eq :
    chi174InputQChi = outerEnclosure 24 chi174QChiValue := by
  rfl'

theorem chi174RoundedFacts :
    ChiRoundedFacts 8 chi174Slice chi174LogChiCertificate
      chi174InputQChi :=
  { coversQChi := by
      rw [chi174InputQChi_eq, chi174QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi175Slice : ChiSlice :=
  { lo := (9/64), hi := (37/256) }

noncomputable def chi175LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (9/8) }, upper := { exponent := -3, mantissa := (37/32) } }

private noncomputable def chi175QChiValue : RationalEnclosure :=
  { lower := (-817558795648811518412050210139/3289097184234506156583131140080), upper := (-144569307972290091440637264134031284647498600413947769943/608476156215857525494452041277942798304001421238734013440) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi175QChiValue_eq :
    chi175QChiValue =
      (chi175Slice.qChiAD 8 chi175LogChiCertificate).value := by
  norm_num [chi175QChiValue, chi175LogChiCertificate, chi175Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi175LogChi_valid :
    (if chi175Slice.lo = 0 then
      if chi175Slice.hi = 0 then true
      else decide (chi175Slice.hi ≤ 1 / 4) &&
        chi175LogChiCertificate.check
          (IntervalAD.const chi175Slice.hi).value
    else chi175LogChiCertificate.check
      chi175Slice.chiAD.value) = true := by
  norm_num [chi175Slice, chi175LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi175ValidityFacts :
    ChiFacts chi175Slice chi175LogChiCertificate :=
  { domain := by norm_num [chi175Slice]
    onePlusPositive := by
      norm_num [chi175Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi175LogChi_valid }

noncomputable def chi175InputQChi : RationalEnclosure :=
  { lower := (-4170251/16777216), upper := (-1993069/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi175InputQChi_eq :
    chi175InputQChi = outerEnclosure 24 chi175QChiValue := by
  rfl'

theorem chi175RoundedFacts :
    ChiRoundedFacts 8 chi175Slice chi175LogChiCertificate
      chi175InputQChi :=
  { coversQChi := by
      rw [chi175InputQChi_eq, chi175QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi176Slice : ChiSlice :=
  { lo := (37/256), hi := (19/128) }

noncomputable def chi176LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (37/32) }, upper := { exponent := -3, mantissa := (19/16) } }

private noncomputable def chi176QChiValue : RationalEnclosure :=
  { lower := (-8444813185249835342763947749959721/33663503561816647795823470539325710), upper := (-388653667508228398694150580187134174047983281125425455737/1619332083083557091480072351051853211521400467187500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi176QChiValue_eq :
    chi176QChiValue =
      (chi176Slice.qChiAD 8 chi176LogChiCertificate).value := by
  norm_num [chi176QChiValue, chi176LogChiCertificate, chi176Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi176LogChi_valid :
    (if chi176Slice.lo = 0 then
      if chi176Slice.hi = 0 then true
      else decide (chi176Slice.hi ≤ 1 / 4) &&
        chi176LogChiCertificate.check
          (IntervalAD.const chi176Slice.hi).value
    else chi176LogChiCertificate.check
      chi176Slice.chiAD.value) = true := by
  norm_num [chi176Slice, chi176LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi176ValidityFacts :
    ChiFacts chi176Slice chi176LogChiCertificate :=
  { domain := by norm_num [chi176Slice]
    onePlusPositive := by
      norm_num [chi176Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi176LogChi_valid }

noncomputable def chi176InputQChi : RationalEnclosure :=
  { lower := (-2104363/8388608), upper := (-1006669/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi176InputQChi_eq :
    chi176InputQChi = outerEnclosure 24 chi176QChiValue := by
  rfl'

theorem chi176RoundedFacts :
    ChiRoundedFacts 8 chi176Slice chi176LogChiCertificate
      chi176InputQChi :=
  { coversQChi := by
      rw [chi176InputQChi_eq, chi176QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi177Slice : ChiSlice :=
  { lo := (19/128), hi := (39/256) }

noncomputable def chi177LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (19/16) }, upper := { exponent := -3, mantissa := (39/32) } }

private noncomputable def chi177QChiValue : RationalEnclosure :=
  { lower := (-11342031784014910107678188108591723/44821691548109078076463623046875000), upper := (-46969254292429396704803022207033880149411246099479321312043308034469/193834050118119410285552793146186230296099092116658745703125000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi177QChiValue_eq :
    chi177QChiValue =
      (chi177Slice.qChiAD 8 chi177LogChiCertificate).value := by
  norm_num [chi177QChiValue, chi177LogChiCertificate, chi177Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi177LogChi_valid :
    (if chi177Slice.lo = 0 then
      if chi177Slice.hi = 0 then true
      else decide (chi177Slice.hi ≤ 1 / 4) &&
        chi177LogChiCertificate.check
          (IntervalAD.const chi177Slice.hi).value
    else chi177LogChiCertificate.check
      chi177Slice.chiAD.value) = true := by
  norm_num [chi177Slice, chi177LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi177ValidityFacts :
    ChiFacts chi177Slice chi177LogChiCertificate :=
  { domain := by norm_num [chi177Slice]
    onePlusPositive := by
      norm_num [chi177Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi177LogChi_valid }

noncomputable def chi177InputQChi : RationalEnclosure :=
  { lower := (-4245439/16777216), upper := (-4065401/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi177InputQChi_eq :
    chi177InputQChi = outerEnclosure 24 chi177QChiValue := by
  rfl'

theorem chi177RoundedFacts :
    ChiRoundedFacts 8 chi177Slice chi177LogChiCertificate
      chi177InputQChi :=
  { coversQChi := by
      rw [chi177InputQChi_eq, chi177QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi178Slice : ChiSlice :=
  { lo := (39/256), hi := (5/32) }

noncomputable def chi178LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (39/32) }, upper := { exponent := -3, mantissa := (5/4) } }

private noncomputable def chi178QChiValue : RationalEnclosure :=
  { lower := (-6349201096324384607477330030537763452482/24885716255805530403988032165136832853315), upper := (-4135195028624411221782374737535281649374713906099559/16911442742744122030774243837530382214157028272748800) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi178QChiValue_eq :
    chi178QChiValue =
      (chi178Slice.qChiAD 8 chi178LogChiCertificate).value := by
  norm_num [chi178QChiValue, chi178LogChiCertificate, chi178Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi178LogChi_valid :
    (if chi178Slice.lo = 0 then
      if chi178Slice.hi = 0 then true
      else decide (chi178Slice.hi ≤ 1 / 4) &&
        chi178LogChiCertificate.check
          (IntervalAD.const chi178Slice.hi).value
    else chi178LogChiCertificate.check
      chi178Slice.chiAD.value) = true := by
  norm_num [chi178Slice, chi178LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi178ValidityFacts :
    ChiFacts chi178Slice chi178LogChiCertificate :=
  { domain := by norm_num [chi178Slice]
    onePlusPositive := by
      norm_num [chi178Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi178LogChi_valid }

noncomputable def chi178InputQChi : RationalEnclosure :=
  { lower := (-4280445/16777216), upper := (-4102373/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi178InputQChi_eq :
    chi178InputQChi = outerEnclosure 24 chi178QChiValue := by
  rfl'

theorem chi178RoundedFacts :
    ChiRoundedFacts 8 chi178Slice chi178LogChiCertificate
      chi178InputQChi :=
  { coversQChi := by
      rw [chi178InputQChi_eq, chi178QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi179Slice : ChiSlice :=
  { lo := (17/128), hi := (35/256) }

noncomputable def chi179LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (17/16) }, upper := { exponent := -3, mantissa := (35/32) } }

private noncomputable def chi179QChiValue : RationalEnclosure :=
  { lower := (-660691451144603818888120093/2711637894368671625385994680), upper := (-48144950356454227633805473817298664475498299879823535983447/207145473450100060795768329906375339121750826699711939289600) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi179QChiValue_eq :
    chi179QChiValue =
      (chi179Slice.qChiAD 8 chi179LogChiCertificate).value := by
  norm_num [chi179QChiValue, chi179LogChiCertificate, chi179Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi179LogChi_valid :
    (if chi179Slice.lo = 0 then
      if chi179Slice.hi = 0 then true
      else decide (chi179Slice.hi ≤ 1 / 4) &&
        chi179LogChiCertificate.check
          (IntervalAD.const chi179Slice.hi).value
    else chi179LogChiCertificate.check
      chi179Slice.chiAD.value) = true := by
  norm_num [chi179Slice, chi179LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi179ValidityFacts :
    ChiFacts chi179Slice chi179LogChiCertificate :=
  { domain := by norm_num [chi179Slice]
    onePlusPositive := by
      norm_num [chi179Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi179LogChi_valid }

noncomputable def chi179InputQChi : RationalEnclosure :=
  { lower := (-4087775/16777216), upper := (-243711/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi179InputQChi_eq :
    chi179InputQChi = outerEnclosure 24 chi179QChiValue := by
  rfl'

theorem chi179RoundedFacts :
    ChiRoundedFacts 8 chi179Slice chi179LogChiCertificate
      chi179InputQChi :=
  { coversQChi := by
      rw [chi179InputQChi_eq, chi179QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi180Slice : ChiSlice :=
  { lo := (35/256), hi := (9/64) }

noncomputable def chi180LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (35/32) }, upper := { exponent := -3, mantissa := (9/8) } }

private noncomputable def chi180QChiValue : RationalEnclosure :=
  { lower := (-1406762506441305038470351089932942062861/5714726134939109087900876311348631313495), upper := (-49748296488882267753004977782128240578157566508383494608082147/211636819315533825592388319000305717270481596533956900675613440) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi180QChiValue_eq :
    chi180QChiValue =
      (chi180Slice.qChiAD 8 chi180LogChiCertificate).value := by
  norm_num [chi180QChiValue, chi180LogChiCertificate, chi180Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi180LogChi_valid :
    (if chi180Slice.lo = 0 then
      if chi180Slice.hi = 0 then true
      else decide (chi180Slice.hi ≤ 1 / 4) &&
        chi180LogChiCertificate.check
          (IntervalAD.const chi180Slice.hi).value
    else chi180LogChiCertificate.check
      chi180Slice.chiAD.value) = true := by
  norm_num [chi180Slice, chi180LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi180ValidityFacts :
    ChiFacts chi180Slice chi180LogChiCertificate :=
  { domain := by norm_num [chi180Slice]
    onePlusPositive := by
      norm_num [chi180Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi180LogChi_valid }

noncomputable def chi180InputQChi : RationalEnclosure :=
  { lower := (-4129955/16777216), upper := (-3943727/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi180InputQChi_eq :
    chi180InputQChi = outerEnclosure 24 chi180QChiValue := by
  rfl'

theorem chi180RoundedFacts :
    ChiRoundedFacts 8 chi180Slice chi180LogChiCertificate
      chi180InputQChi :=
  { coversQChi := by
      rw [chi180InputQChi_eq, chi180QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi181Slice : ChiSlice :=
  { lo := (1/8), hi := (33/256) }

noncomputable def chi181LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (1) }, upper := { exponent := -3, mantissa := (33/32) } }

private noncomputable def chi181QChiValue : RationalEnclosure :=
  { lower := (-597351034279/2507041031040), upper := (-641480695881828862167245974970723563265317/2828764799664842260883178267750000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi181QChiValue_eq :
    chi181QChiValue =
      (chi181Slice.qChiAD 8 chi181LogChiCertificate).value := by
  norm_num [chi181QChiValue, chi181LogChiCertificate, chi181Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi181LogChi_valid :
    (if chi181Slice.lo = 0 then
      if chi181Slice.hi = 0 then true
      else decide (chi181Slice.hi ≤ 1 / 4) &&
        chi181LogChiCertificate.check
          (IntervalAD.const chi181Slice.hi).value
    else chi181LogChiCertificate.check
      chi181Slice.chiAD.value) = true := by
  norm_num [chi181Slice, chi181LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi181ValidityFacts :
    ChiFacts chi181Slice chi181LogChiCertificate :=
  { domain := by norm_num [chi181Slice]
    onePlusPositive := by
      norm_num [chi181Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi181LogChi_valid }

noncomputable def chi181InputQChi : RationalEnclosure :=
  { lower := (-3997497/16777216), upper := (-3804579/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi181InputQChi_eq :
    chi181InputQChi = outerEnclosure 24 chi181QChiValue := by
  rfl'

theorem chi181RoundedFacts :
    ChiRoundedFacts 8 chi181Slice chi181LogChiCertificate
      chi181InputQChi :=
  { coversQChi := by
      rw [chi181InputQChi_eq, chi181QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi182Slice : ChiSlice :=
  { lo := (33/256), hi := (17/128) }

noncomputable def chi182LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (33/32) }, upper := { exponent := -3, mantissa := (17/16) } }

private noncomputable def chi182QChiValue : RationalEnclosure :=
  { lower := (-4159709129617502118438842964848079763/17258772164910163285812415466308593750), upper := (-137250328346122583837545829281791731112458185469404602541213/597629771088362390767282811745839575837263420117187500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi182QChiValue_eq :
    chi182QChiValue =
      (chi182Slice.qChiAD 8 chi182LogChiCertificate).value := by
  norm_num [chi182QChiValue, chi182LogChiCertificate, chi182Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi182LogChi_valid :
    (if chi182Slice.lo = 0 then
      if chi182Slice.hi = 0 then true
      else decide (chi182Slice.hi ≤ 1 / 4) &&
        chi182LogChiCertificate.check
          (IntervalAD.const chi182Slice.hi).value
    else chi182LogChiCertificate.check
      chi182Slice.chiAD.value) = true := by
  norm_num [chi182Slice, chi182LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi182ValidityFacts :
    ChiFacts chi182Slice chi182LogChiCertificate :=
  { domain := by norm_num [chi182Slice]
    onePlusPositive := by
      norm_num [chi182Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi182LogChi_valid }

noncomputable def chi182InputQChi : RationalEnclosure :=
  { lower := (-4043645/16777216), upper := (-1926509/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi182InputQChi_eq :
    chi182InputQChi = outerEnclosure 24 chi182QChiValue := by
  rfl'

theorem chi182RoundedFacts :
    ChiRoundedFacts 8 chi182Slice chi182LogChiCertificate
      chi182InputQChi :=
  { coversQChi := by
      rw [chi182InputQChi_eq, chi182QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi183Slice : ChiSlice :=
  { lo := (5/32), hi := (41/256) }

noncomputable def chi183LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (5/4) }, upper := { exponent := -3, mantissa := (41/32) } }

private noncomputable def chi183QChiValue : RationalEnclosure :=
  { lower := (-941140650450318750847/3660283132506967206240), upper := (-232138807996168617195144763038333484696560829223525771/941269742156274069150799289276220447101881204580075520) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi183QChiValue_eq :
    chi183QChiValue =
      (chi183Slice.qChiAD 8 chi183LogChiCertificate).value := by
  norm_num [chi183QChiValue, chi183LogChiCertificate, chi183Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi183LogChi_valid :
    (if chi183Slice.lo = 0 then
      if chi183Slice.hi = 0 then true
      else decide (chi183Slice.hi ≤ 1 / 4) &&
        chi183LogChiCertificate.check
          (IntervalAD.const chi183Slice.hi).value
    else chi183LogChiCertificate.check
      chi183Slice.chiAD.value) = true := by
  norm_num [chi183Slice, chi183LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi183ValidityFacts :
    ChiFacts chi183Slice chi183LogChiCertificate :=
  { domain := by norm_num [chi183Slice]
    onePlusPositive := by
      norm_num [chi183Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi183LogChi_valid }

noncomputable def chi183InputQChi : RationalEnclosure :=
  { lower := (-2156899/8388608), upper := (-258603/1048576) }

set_option maxRecDepth 1000000 in
private theorem chi183InputQChi_eq :
    chi183InputQChi = outerEnclosure 24 chi183QChiValue := by
  rfl'

theorem chi183RoundedFacts :
    ChiRoundedFacts 8 chi183Slice chi183LogChiCertificate
      chi183InputQChi :=
  { coversQChi := by
      rw [chi183InputQChi_eq, chi183QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi184Slice : ChiSlice :=
  { lo := (41/256), hi := (21/128) }

noncomputable def chi184LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (41/32) }, upper := { exponent := -3, mantissa := (21/16) } }

private noncomputable def chi184QChiValue : RationalEnclosure :=
  { lower := (-4687677410405100593506766305175084161519/18098098796153691802389800156232071099430), upper := (-7804280028599938001384666801856069193012644646593938831094794907613/31389444011851734214515998305479601440416689495435650633738483997440) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi184QChiValue_eq :
    chi184QChiValue =
      (chi184Slice.qChiAD 8 chi184LogChiCertificate).value := by
  norm_num [chi184QChiValue, chi184LogChiCertificate, chi184Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi184LogChi_valid :
    (if chi184Slice.lo = 0 then
      if chi184Slice.hi = 0 then true
      else decide (chi184Slice.hi ≤ 1 / 4) &&
        chi184LogChiCertificate.check
          (IntervalAD.const chi184Slice.hi).value
    else chi184LogChiCertificate.check
      chi184Slice.chiAD.value) = true := by
  norm_num [chi184Slice, chi184LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi184ValidityFacts :
    ChiFacts chi184Slice chi184LogChiCertificate :=
  { domain := by norm_num [chi184Slice]
    onePlusPositive := by
      norm_num [chi184Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi184LogChi_valid }

noncomputable def chi184InputQChi : RationalEnclosure :=
  { lower := (-2172775/8388608), upper := (-4171277/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi184InputQChi_eq :
    chi184InputQChi = outerEnclosure 24 chi184QChiValue := by
  rfl'

theorem chi184RoundedFacts :
    ChiRoundedFacts 8 chi184Slice chi184LogChiCertificate
      chi184InputQChi :=
  { coversQChi := by
      rw [chi184InputQChi_eq, chi184QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi185Slice : ChiSlice :=
  { lo := (21/128), hi := (43/256) }

noncomputable def chi185LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (21/16) }, upper := { exponent := -3, mantissa := (43/32) } }

private noncomputable def chi185QChiValue : RationalEnclosure :=
  { lower := (-7444874973083175638769809717855043721/28544669503843055365434423681709779960), upper := (-1096091187557834395298650788441275701764117660658864421698361089/4374966809879662547509555641123564731427669525146484375000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi185QChiValue_eq :
    chi185QChiValue =
      (chi185Slice.qChiAD 8 chi185LogChiCertificate).value := by
  norm_num [chi185QChiValue, chi185LogChiCertificate, chi185Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi185LogChi_valid :
    (if chi185Slice.lo = 0 then
      if chi185Slice.hi = 0 then true
      else decide (chi185Slice.hi ≤ 1 / 4) &&
        chi185LogChiCertificate.check
          (IntervalAD.const chi185Slice.hi).value
    else chi185LogChiCertificate.check
      chi185Slice.chiAD.value) = true := by
  norm_num [chi185Slice, chi185LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi185ValidityFacts :
    ChiFacts chi185Slice chi185LogChiCertificate :=
  { domain := by norm_num [chi185Slice]
    onePlusPositive := by
      norm_num [chi185Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi185LogChi_valid }

noncomputable def chi185InputQChi : RationalEnclosure :=
  { lower := (-1093937/4194304), upper := (-4203313/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi185InputQChi_eq :
    chi185InputQChi = outerEnclosure 24 chi185QChiValue := by
  rfl'

theorem chi185RoundedFacts :
    ChiRoundedFacts 8 chi185Slice chi185LogChiCertificate
      chi185InputQChi :=
  { coversQChi := by
      rw [chi185InputQChi_eq, chi185QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi186Slice : ChiSlice :=
  { lo := (43/256), hi := (11/64) }

noncomputable def chi186LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (43/32) }, upper := { exponent := -3, mantissa := (11/8) } }

private noncomputable def chi186QChiValue : RationalEnclosure :=
  { lower := (-1431837134778249144739291554569917/5454096159380860626697540283203125), upper := (-1470992221723915916780836679326021812906040185534236836997/5829072594661402888246629716966181993484497070312500000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi186QChiValue_eq :
    chi186QChiValue =
      (chi186Slice.qChiAD 8 chi186LogChiCertificate).value := by
  norm_num [chi186QChiValue, chi186LogChiCertificate, chi186Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi186LogChi_valid :
    (if chi186Slice.lo = 0 then
      if chi186Slice.hi = 0 then true
      else decide (chi186Slice.hi ≤ 1 / 4) &&
        chi186LogChiCertificate.check
          (IntervalAD.const chi186Slice.hi).value
    else chi186LogChiCertificate.check
      chi186Slice.chiAD.value) = true := by
  norm_num [chi186Slice, chi186LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi186ValidityFacts :
    ChiFacts chi186Slice chi186LogChiCertificate :=
  { domain := by norm_num [chi186Slice]
    onePlusPositive := by
      norm_num [chi186Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi186LogChi_valid }

noncomputable def chi186InputQChi : RationalEnclosure :=
  { lower := (-4404441/16777216), upper := (-1058451/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi186InputQChi_eq :
    chi186InputQChi = outerEnclosure 24 chi186QChiValue := by
  rfl'

theorem chi186RoundedFacts :
    ChiRoundedFacts 8 chi186Slice chi186LogChiCertificate
      chi186InputQChi :=
  { coversQChi := by
      rw [chi186InputQChi_eq, chi186QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi187Slice : ChiSlice :=
  { lo := (3/16), hi := (49/256) }

noncomputable def chi187LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (3/2) }, upper := { exponent := -3, mantissa := (49/32) } }

private noncomputable def chi187QChiValue : RationalEnclosure :=
  { lower := (-5406631252372249565519/20038024423828125000000), upper := (-3075580129609153215485055108446015009144668800739/11822231681109748906956806569240134375000000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi187QChiValue_eq :
    chi187QChiValue =
      (chi187Slice.qChiAD 8 chi187LogChiCertificate).value := by
  norm_num [chi187QChiValue, chi187LogChiCertificate, chi187Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi187LogChi_valid :
    (if chi187Slice.lo = 0 then
      if chi187Slice.hi = 0 then true
      else decide (chi187Slice.hi ≤ 1 / 4) &&
        chi187LogChiCertificate.check
          (IntervalAD.const chi187Slice.hi).value
    else chi187LogChiCertificate.check
      chi187Slice.chiAD.value) = true := by
  norm_num [chi187Slice, chi187LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi187ValidityFacts :
    ChiFacts chi187Slice chi187LogChiCertificate :=
  { domain := by norm_num [chi187Slice]
    onePlusPositive := by
      norm_num [chi187Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi187LogChi_valid }

noncomputable def chi187InputQChi : RationalEnclosure :=
  { lower := (-4526805/16777216), upper := (-2182315/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi187InputQChi_eq :
    chi187InputQChi = outerEnclosure 24 chi187QChiValue := by
  rfl'

theorem chi187RoundedFacts :
    ChiRoundedFacts 8 chi187Slice chi187LogChiCertificate
      chi187InputQChi :=
  { coversQChi := by
      rw [chi187InputQChi_eq, chi187QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi188Slice : ChiSlice :=
  { lo := (49/256), hi := (25/128) }

noncomputable def chi188LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (49/32) }, upper := { exponent := -3, mantissa := (25/16) } }

private noncomputable def chi188QChiValue : RationalEnclosure :=
  { lower := (-4209468857450261803080550009827439/15530679092657859616717994314117566), upper := (-1717673736685271335826622984865327478872570439134404258378298933/6569271345445300068918007558788942389881702575593378168125152000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi188QChiValue_eq :
    chi188QChiValue =
      (chi188Slice.qChiAD 8 chi188LogChiCertificate).value := by
  norm_num [chi188QChiValue, chi188LogChiCertificate, chi188Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi188LogChi_valid :
    (if chi188Slice.lo = 0 then
      if chi188Slice.hi = 0 then true
      else decide (chi188Slice.hi ≤ 1 / 4) &&
        chi188LogChiCertificate.check
          (IntervalAD.const chi188Slice.hi).value
    else chi188LogChiCertificate.check
      chi188Slice.chiAD.value) = true := by
  norm_num [chi188Slice, chi188LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi188ValidityFacts :
    ChiFacts chi188Slice chi188LogChiCertificate :=
  { domain := by norm_num [chi188Slice]
    onePlusPositive := by
      norm_num [chi188Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi188LogChi_valid }

noncomputable def chi188InputQChi : RationalEnclosure :=
  { lower := (-4547333/16777216), upper := (-2193377/8388608) }

set_option maxRecDepth 1000000 in
private theorem chi188InputQChi_eq :
    chi188InputQChi = outerEnclosure 24 chi188QChiValue := by
  rfl'

theorem chi188RoundedFacts :
    ChiRoundedFacts 8 chi188Slice chi188LogChiCertificate
      chi188InputQChi :=
  { coversQChi := by
      rw [chi188InputQChi_eq, chi188QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi189Slice : ChiSlice :=
  { lo := (31/128), hi := (63/256) }

noncomputable def chi189LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (31/16) }, upper := { exponent := -3, mantissa := (63/32) } }

private noncomputable def chi189QChiValue : RationalEnclosure :=
  { lower := (-4914057079772440570486650975626117897/17491914002438716585207803487853139720), upper := (-3245621304233497826936267369474364008173615267668980545329976651363349/11912271038559428930689317721297953271408590993051755944685625000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi189QChiValue_eq :
    chi189QChiValue =
      (chi189Slice.qChiAD 8 chi189LogChiCertificate).value := by
  norm_num [chi189QChiValue, chi189LogChiCertificate, chi189Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi189LogChi_valid :
    (if chi189Slice.lo = 0 then
      if chi189Slice.hi = 0 then true
      else decide (chi189Slice.hi ≤ 1 / 4) &&
        chi189LogChiCertificate.check
          (IntervalAD.const chi189Slice.hi).value
    else chi189LogChiCertificate.check
      chi189Slice.chiAD.value) = true := by
  norm_num [chi189Slice, chi189LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi189ValidityFacts :
    ChiFacts chi189Slice chi189LogChiCertificate :=
  { domain := by norm_num [chi189Slice]
    onePlusPositive := by
      norm_num [chi189Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi189LogChi_valid }

noncomputable def chi189InputQChi : RationalEnclosure :=
  { lower := (-4713275/16777216), upper := (-4571125/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi189InputQChi_eq :
    chi189InputQChi = outerEnclosure 24 chi189QChiValue := by
  rfl'

theorem chi189RoundedFacts :
    ChiRoundedFacts 8 chi189Slice chi189LogChiCertificate
      chi189InputQChi :=
  { coversQChi := by
      rw [chi189InputQChi_eq, chi189QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi190Slice : ChiSlice :=
  { lo := (63/256), hi := (1/4) }

noncomputable def chi190LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (63/32) }, upper := { exponent := -2, mantissa := (1) } }

private noncomputable def chi190QChiValue : RationalEnclosure :=
  { lower := (-2985507850503183716027619132314507030215568/10613720944714131671477653716974945068359375), upper := (-1348134076641533331202252805452258654021731019/4940204657903304923451417002810156250000000000) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi190QChiValue_eq :
    chi190QChiValue =
      (chi190Slice.qChiAD 8 chi190LogChiCertificate).value := by
  norm_num [chi190QChiValue, chi190LogChiCertificate, chi190Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi190LogChi_valid :
    (if chi190Slice.lo = 0 then
      if chi190Slice.hi = 0 then true
      else decide (chi190Slice.hi ≤ 1 / 4) &&
        chi190LogChiCertificate.check
          (IntervalAD.const chi190Slice.hi).value
    else chi190LogChiCertificate.check
      chi190Slice.chiAD.value) = true := by
  norm_num [chi190Slice, chi190LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi190ValidityFacts :
    ChiFacts chi190Slice chi190LogChiCertificate :=
  { domain := by norm_num [chi190Slice]
    onePlusPositive := by
      norm_num [chi190Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi190LogChi_valid }

noncomputable def chi190InputQChi : RationalEnclosure :=
  { lower := (-4719223/16777216), upper := (-1144585/4194304) }

set_option maxRecDepth 1000000 in
private theorem chi190InputQChi_eq :
    chi190InputQChi = outerEnclosure 24 chi190QChiValue := by
  rfl'

theorem chi190RoundedFacts :
    ChiRoundedFacts 8 chi190Slice chi190LogChiCertificate
      chi190InputQChi :=
  { coversQChi := by
      rw [chi190InputQChi_eq, chi190QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

noncomputable def chi191Slice : ChiSlice :=
  { lo := (15/64), hi := (61/256) }

noncomputable def chi191LogChiCertificate :
    RationalEnclosure.LogIntervalCertificate :=
  { lower := { exponent := -3, mantissa := (15/8) }, upper := { exponent := -3, mantissa := (61/32) } }

private noncomputable def chi191QChiValue : RationalEnclosure :=
  { lower := (-6778719666444846414786688693314029/24204020763444961782662609079469680), upper := (-190789197562747244346263848630636139884775904743750582006666737/702881310332793245768138263207618647281908946454761091449226240) }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi191QChiValue_eq :
    chi191QChiValue =
      (chi191Slice.qChiAD 8 chi191LogChiCertificate).value := by
  norm_num [chi191QChiValue, chi191LogChiCertificate, chi191Slice,
    ChiSlice.qChiAD, ChiSlice.qChiEndpointAD,
    ChiSlice.qChiEndpointRawAD, ChiSlice.chiAD, ChiSlice.onePlusAD,
    IntervalAD.log, IntervalAD.unary, IntervalAD.const,
    IntervalAD.variableChi, IntervalAD.add, IntervalAD.mul,
    IntervalAD.invPositive, IntervalAD.divPositive,
    RationalEnclosure.LogIntervalCertificate.enclosure,
    RationalEnclosure.LogRangeCertificate.enclosure,
    RationalEnclosure.logScaledMantissaEnclosure,
    RationalEnclosure.logTwoEnclosure,
    RationalEnclosure.logMantissaEnclosure,
    RationalEnclosure.halfLogRatioEnclosure,
    RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
    RationalEnclosure.logRatioCoordinate, RationalEnclosure.point,
    RationalEnclosure.add, RationalEnclosure.neg,
    RationalEnclosure.sub, RationalEnclosure.mul,
    RationalEnclosure.div, RationalEnclosure.mulNonnegative,
    RationalEnclosure.scale, RationalEnclosure.invPositive,
    RationalEnclosure.center, RationalEnclosure.radius,
    RationalEnclosure.mk.injEq]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem chi191LogChi_valid :
    (if chi191Slice.lo = 0 then
      if chi191Slice.hi = 0 then true
      else decide (chi191Slice.hi ≤ 1 / 4) &&
        chi191LogChiCertificate.check
          (IntervalAD.const chi191Slice.hi).value
    else chi191LogChiCertificate.check
      chi191Slice.chiAD.value) = true := by
  norm_num [chi191Slice, chi191LogChiCertificate,
    ChiSlice.chiAD,
    RationalEnclosure.LogIntervalCertificate.check,
    RationalEnclosure.LogRangeCertificate.check, IntervalAD.const,
    IntervalAD.variableChi, RationalEnclosure.point]

theorem chi191ValidityFacts :
    ChiFacts chi191Slice chi191LogChiCertificate :=
  { domain := by norm_num [chi191Slice]
    onePlusPositive := by
      norm_num [chi191Slice, ChiSlice.onePlusAD, ChiSlice.chiAD,
        IntervalAD.const, IntervalAD.variableChi, IntervalAD.add,
        RationalEnclosure.point, RationalEnclosure.add]
    logChi := chi191LogChi_valid }

noncomputable def chi191InputQChi : RationalEnclosure :=
  { lower := (-2349363/8388608), upper := (-4553985/16777216) }

set_option maxRecDepth 1000000 in
private theorem chi191InputQChi_eq :
    chi191InputQChi = outerEnclosure 24 chi191QChiValue := by
  rfl'

theorem chi191RoundedFacts :
    ChiRoundedFacts 8 chi191Slice chi191LogChiCertificate
      chi191InputQChi :=
  { coversQChi := by
      rw [chi191InputQChi_eq, chi191QChiValue_eq]
      exact outerEnclosure_covers 24 _ }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
