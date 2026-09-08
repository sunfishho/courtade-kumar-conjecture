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

noncomputable def endpoint64 : EndpointCache :=
  { input := (117/64), certificate := { exponent := 0, mantissa := (117/64) }, enclosure := { lower := (199228724142214108084168723844954263936/330236607605274292708960987452050956545), upper := (25501276769298675802441932882497730493813/42270285773475109466747006393862522437760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint64_valid : endpoint64.Valid 8 := by
  constructor
  · norm_num [endpoint64, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint64, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint64PositiveFacts : PositiveEndpointFacts 8
    endpoint64 :=
  { valid := endpoint64_valid
    positive := by
      norm_num [endpoint64] }

noncomputable def endpoint65 : EndpointCache :=
  { input := (435/256), certificate := { exponent := 0, mantissa := (435/256) }, enclosure := { lower := (93375145881457491170632363067458585259161737856/176123497774582938720516209529815409022295858295), upper := (277286833328998857173855921820212844754902878906573/523016338991401494824444935819739838632609780792832) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint65_valid : endpoint65.Valid 8 := by
  constructor
  · norm_num [endpoint65, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint65, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint65PositiveFacts : PositiveEndpointFacts 8
    endpoint65 :=
  { valid := endpoint65_valid
    positive := by
      norm_num [endpoint65] }

noncomputable def endpoint66 : EndpointCache :=
  { input := (225/128), certificate := { exponent := 0, mantissa := (225/128) }, enclosure := { lower := (4184082902398655996379834100120063408875392/7417664256067839520807743928301782165004565), upper := (1785208707011499458130942344256048601194268099/3164870082588944862211304076075427057068614400) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint66_valid : endpoint66.Valid 8 := by
  constructor
  · norm_num [endpoint66, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint66, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint66PositiveFacts : PositiveEndpointFacts 8
    endpoint66 :=
  { valid := endpoint66_valid
    positive := by
      norm_num [endpoint66] }

noncomputable def endpoint67 : EndpointCache :=
  { input := (115/64), certificate := { exponent := 0, mantissa := (115/64) }, enclosure := { lower := (18202603496250759544459660768087449216/31059863766618305830833367136194298495), upper := (10717692959979801660262724543431700336751/18288047785784858473194686569791202953856) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint67_valid : endpoint67.Valid 8 := by
  constructor
  · norm_num [endpoint67, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint67, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint67PositiveFacts : PositiveEndpointFacts 8
    endpoint67 :=
  { valid := endpoint67_valid
    positive := by
      norm_num [endpoint67] }

noncomputable def endpoint68 : EndpointCache :=
  { input := (57/32), certificate := { exponent := 0, mantissa := (57/32) }, enclosure := { lower := (905607066731927058644738253347200/1568652285499292565660784758703641), upper := (1101218194893999360543427955083867075/1907481179167139759843514266583627456) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint68_valid : endpoint68.Valid 8 := by
  constructor
  · norm_num [endpoint68, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint68, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint68PositiveFacts : PositiveEndpointFacts 8
    endpoint68 :=
  { valid := endpoint68_valid
    positive := by
      norm_num [endpoint68] }

noncomputable def endpoint69 : EndpointCache :=
  { input := (121/64), certificate := { exponent := 0, mantissa := (121/64) }, enclosure := { lower := (32438169958909963754520594828111011712/50930742526209582885067976837158203125), upper := (45672943624166042679776161330768343956431/71710485476903092702175711386718750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint69_valid : endpoint69.Valid 8 := by
  constructor
  · norm_num [endpoint69, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint69, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint69PositiveFacts : PositiveEndpointFacts 8
    endpoint69 :=
  { valid := endpoint69_valid
    positive := by
      norm_num [endpoint69] }

noncomputable def endpoint70 : EndpointCache :=
  { input := (61/32), certificate := { exponent := 0, mantissa := (61/32) }, enclosure := { lower := (3261535892043051462482412905465984/5055563443704986565148927334558355), upper := (12733036231502146176533387802233408171/19736919684224267550341412314115817920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint70_valid : endpoint70.Valid 8 := by
  constructor
  · norm_num [endpoint70, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint70, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint70PositiveFacts : PositiveEndpointFacts 8
    endpoint70 :=
  { valid := endpoint70_valid
    positive := by
      norm_num [endpoint70] }

noncomputable def endpoint71 : EndpointCache :=
  { input := (125/64), certificate := { exponent := 0, mantissa := (125/64) }, enclosure := { lower := (20140022621703373701740271470421614464/30085300875536192933393279054180263605), upper := (9206867621600838911416382951127249525887/13753280400245116769551213281910977648000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint71_valid : endpoint71.Valid 8 := by
  constructor
  · norm_num [endpoint71, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint71, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint71PositiveFacts : PositiveEndpointFacts 8
    endpoint71 :=
  { valid := endpoint71_valid
    positive := by
      norm_num [endpoint71] }

noncomputable def endpoint72 : EndpointCache :=
  { input := (33/16), certificate := { exponent := 1, mantissa := (33/32) }, enclosure := { lower := (18740925441958589353620009377447236928/25888158247365244928718623199462890625), upper := (1199419257152393874527590919981344125137/1656842127831375675437991884765625000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint72_valid : endpoint72.Valid 8 := by
  constructor
  · norm_num [endpoint72, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint72, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint72PositiveFacts : PositiveEndpointFacts 8
    endpoint72 :=
  { valid := endpoint72_valid
    positive := by
      norm_num [endpoint72] }

noncomputable def endpoint73 : EndpointCache :=
  { input := (17/8), certificate := { exponent := 1, mantissa := (17/16) }, enclosure := { lower := (6852343516287805272866368/9090740067327922115757645), upper := (3727674959023271642919465637/4945362596626389630972158880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint73_valid : endpoint73.Valid 8 := by
  constructor
  · norm_num [endpoint73, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint73, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint73PositiveFacts : PositiveEndpointFacts 8
    endpoint73 :=
  { valid := endpoint73_valid
    positive := by
      norm_num [endpoint73] }

noncomputable def endpoint74 : EndpointCache :=
  { input := (35/16), certificate := { exponent := 1, mantissa := (35/32) }, enclosure := { lower := (83008860264666772344943573789354033088/106046464359694807816717292375541612003), upper := (26562835875938201950384203850167022358269/33934868595102338501349533560173315840960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint74_valid : endpoint74.Valid 8 := by
  constructor
  · norm_num [endpoint74, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint74, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint74PositiveFacts : PositiveEndpointFacts 8
    endpoint74 :=
  { valid := endpoint74_valid
    positive := by
      norm_num [endpoint74] }

noncomputable def endpoint75 : EndpointCache :=
  { input := (9/4), certificate := { exponent := 1, mantissa := (9/8) }, enclosure := { lower := (100021060779008004113087080000/123341144408793980871867417753), upper := (1600337006847553760550088337485/1973458310540703693949878684048) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint75_valid : endpoint75.Valid 8 := by
  constructor
  · norm_num [endpoint75, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint75, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint75PositiveFacts : PositiveEndpointFacts 8
    endpoint75 :=
  { valid := endpoint75_valid
    positive := by
      norm_num [endpoint75] }

noncomputable def endpoint76 : EndpointCache :=
  { input := (37/16), certificate := { exponent := 1, mantissa := (37/32) }, enclosure := { lower := (6879838530740453340413050186816/8206607401710543099908208322605), upper := (16291457979377480913837187290926293/19433246327250566060582637307928640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint76_valid : endpoint76.Valid 8 := by
  constructor
  · norm_num [endpoint76, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint76, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint76PositiveFacts : PositiveEndpointFacts 8
    endpoint76 :=
  { valid := endpoint76_valid
    positive := by
      norm_num [endpoint76] }

noncomputable def endpoint77 : EndpointCache :=
  { input := (19/8), certificate := { exponent := 1, mantissa := (19/16) }, enclosure := { lower := (350662171432221631629633398002624/405390994985216615255584716796875), upper := (30457514932164980334022256953011341/35211103564430243153627929687500000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint77_valid : endpoint77.Valid 8 := by
  constructor
  · norm_num [endpoint77, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint77, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint77PositiveFacts : PositiveEndpointFacts 8
    endpoint77 :=
  { valid := endpoint77_valid
    positive := by
      norm_num [endpoint77] }

noncomputable def endpoint78 : EndpointCache :=
  { input := (39/16), certificate := { exponent := 1, mantissa := (39/32) }, enclosure := { lower := (1127415221204319824354036010657471607232/1265375402837569342575662652464584721355), upper := (72154575568055469726556768082549161043453/80984025781604437924842409757733422166720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint78_valid : endpoint78.Valid 8 := by
  constructor
  · norm_num [endpoint78, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint78, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint78PositiveFacts : PositiveEndpointFacts 8
    endpoint78 :=
  { valid := endpoint78_valid
    positive := by
      norm_num [endpoint78] }

noncomputable def endpoint79 : EndpointCache :=
  { input := (5/2), certificate := { exponent := 1, mantissa := (5/4) }, enclosure := { lower := (566534376123025472/618291069680230947), upper := (22661375475818699093/24731642787209237880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint79_valid : endpoint79.Valid 8 := by
  constructor
  · norm_num [endpoint79, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint79, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint79PositiveFacts : PositiveEndpointFacts 8
    endpoint79 :=
  { valid := endpoint79_valid
    positive := by
      norm_num [endpoint79] }

noncomputable def endpoint80 : EndpointCache :=
  { input := (71/32), certificate := { exponent := 1, mantissa := (71/64) }, enclosure := { lower := (82988191865023516623133818493521472/104133031496161283017964630126953125), upper := (754196704157714859131554187158090861621/946360990237113740067262558593750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint80_valid : endpoint80.Valid 8 := by
  constructor
  · norm_num [endpoint80, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint80, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint80PositiveFacts : PositiveEndpointFacts 8
    endpoint80 :=
  { valid := endpoint80_valid
    positive := by
      norm_num [endpoint80] }

noncomputable def endpoint81 : EndpointCache :=
  { input := (123/64), certificate := { exponent := 0, mantissa := (123/64) }, enclosure := { lower := (31988325580943545788168419584755880832/48964125695991350114987423593516715085), upper := (167874734385060080775205933406369006893271/256963731652562605403453999018775720766080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint81_valid : endpoint81.Valid 8 := by
  constructor
  · norm_num [endpoint81, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint81, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint81PositiveFacts : PositiveEndpointFacts 8
    endpoint81 :=
  { valid := endpoint81_valid
    positive := by
      norm_num [endpoint81] }

noncomputable def endpoint82 : EndpointCache :=
  { input := (65/32), certificate := { exponent := 1, mantissa := (65/64) }, enclosure := { lower := (8819438379195322507483331489621312/12445384008682401117140390439698577), upper := (5644440701459439982844035465774569461/7965045765556736714969849881407089280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint82_valid : endpoint82.Valid 8 := by
  constructor
  · norm_num [endpoint82, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint82, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint82PositiveFacts : PositiveEndpointFacts 8
    endpoint82 :=
  { valid := endpoint82_valid
    positive := by
      norm_num [endpoint82] }

noncomputable def endpoint83 : EndpointCache :=
  { input := (251/128), certificate := { exponent := 0, mantissa := (251/128) }, enclosure := { lower := (1611684267697436289022348139786640640293504/2393272945134631987675776740317483396513495), upper := (103560385994793993007921848631078139865186807039/153782146362570913000094710225840213126371134720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint83_valid : endpoint83.Valid 8 := by
  constructor
  · norm_num [endpoint83, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint83, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint83PositiveFacts : PositiveEndpointFacts 8
    endpoint83 :=
  { valid := endpoint83_valid
    positive := by
      norm_num [endpoint83] }

noncomputable def endpoint84 : EndpointCache :=
  { input := (263/128), certificate := { exponent := 1, mantissa := (263/256) }, enclosure := { lower := (4276702894319754281165920677216923795576000/5938844249888735256788982022507047015028311), upper := (575883718870655448818478669655009582963666950695/799701011313017534738177163222708922855652246016) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint84_valid : endpoint84.Valid 8 := by
  constructor
  · norm_num [endpoint84, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint84, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint84PositiveFacts : PositiveEndpointFacts 8
    endpoint84 :=
  { valid := endpoint84_valid
    positive := by
      norm_num [endpoint84] }

noncomputable def endpoint85 : EndpointCache :=
  { input := (63/32), certificate := { exponent := 0, mantissa := (63/32) }, enclosure := { lower := (14136604510483435502526877686371456/20868953462546090374098358154296875), upper := (301580901598091121896027181562018183/445204340534316594647431640625000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint85_valid : endpoint85.Valid 8 := by
  constructor
  · norm_num [endpoint85, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint85, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint85PositiveFacts : PositiveEndpointFacts 8
    endpoint85 :=
  { valid := endpoint85_valid
    positive := by
      norm_num [endpoint85] }

noncomputable def endpoint86 : EndpointCache :=
  { input := (133/64), certificate := { exponent := 1, mantissa := (133/128) }, enclosure := { lower := (19513138033258416429169990828111748362688/26676751706125469370369907811142019243515), upper := (94911905654493749139892633736568646071019877/129755720298594283017479231593394781600456960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint86_valid : endpoint86.Valid 8 := by
  constructor
  · norm_num [endpoint86, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint86, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint86PositiveFacts : PositiveEndpointFacts 8
    endpoint86 :=
  { valid := endpoint86_valid
    positive := by
      norm_num [endpoint86] }

noncomputable def endpoint87 : EndpointCache :=
  { input := (131/64), certificate := { exponent := 1, mantissa := (131/128) }, enclosure := { lower := (34901666364080776874690566232970949934697097024/48723960061297593686007814050031668328909832985), upper := (167208901664999637282497737728118836067917545303447/233429532087953728836279721711694575582617165569280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint87_valid : endpoint87.Valid 8 := by
  constructor
  · norm_num [endpoint87, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint87, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint87PositiveFacts : PositiveEndpointFacts 8
    endpoint87 :=
  { valid := endpoint87_valid
    positive := by
      norm_num [endpoint87] }

noncomputable def endpoint88 : EndpointCache :=
  { input := (69/32), certificate := { exponent := 1, mantissa := (69/64) }, enclosure := { lower := (1704478280112666200497583596425229418382016/2218302311891501659826218435801946376867855), upper := (716854881490757674618380520686190790678105467/932954572315511555218341010714418590499852160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint88_valid : endpoint88.Valid 8 := by
  constructor
  · norm_num [endpoint88, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint88, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint88PositiveFacts : PositiveEndpointFacts 8
    endpoint88 :=
  { valid := endpoint88_valid
    positive := by
      norm_num [endpoint88] }

noncomputable def endpoint89 : EndpointCache :=
  { input := (135/64), certificate := { exponent := 1, mantissa := (135/128) }, enclosure := { lower := (64073312683130421158785556140587220129171847872/85844085876676792574589830552001908787307876047), upper := (82013842148845960852400028590452968716864811209741/109880429922146294495474983106562443247754081340160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint89_valid : endpoint89.Valid 8 := by
  constructor
  · norm_num [endpoint89, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint89, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint89PositiveFacts : PositiveEndpointFacts 8
    endpoint89 :=
  { valid := endpoint89_valid
    positive := by
      norm_num [endpoint89] }

noncomputable def endpoint90 : EndpointCache :=
  { input := (41/16), certificate := { exponent := 1, mantissa := (41/32) }, enclosure := { lower := (361242626083058858864874713953622216000/383899065372957098838571518465528780897), upper := (947900668392955536180476998091741069617825/1007351147538639427352411664453547521073728) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint90_valid : endpoint90.Valid 8 := by
  constructor
  · norm_num [endpoint90, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint90, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint90PositiveFacts : PositiveEndpointFacts 8
    endpoint90 :=
  { valid := endpoint90_valid
    positive := by
      norm_num [endpoint90] }

noncomputable def endpoint91 : EndpointCache :=
  { input := (21/8), certificate := { exponent := 1, mantissa := (21/16) }, enclosure := { lower := (5333230871158650217988715305344576/5526200859030018462590556985359405), upper := (170663390958120924954511600950342377/176838427488960590802897823531500960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint91_valid : endpoint91.Valid 8 := by
  constructor
  · norm_num [endpoint91, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint91, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint91PositiveFacts : PositiveEndpointFacts 8
    endpoint91 :=
  { valid := endpoint91_valid
    positive := by
      norm_num [endpoint91] }

noncomputable def endpoint92 : EndpointCache :=
  { input := (43/16), certificate := { exponent := 1, mantissa := (43/32) }, enclosure := { lower := (7346933926052697829015631312576/7431569150649011135101318359375), upper := (20218762520825461769484459462106247/20451678302586078643798828125000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint92_valid : endpoint92.Valid 8 := by
  constructor
  · norm_num [endpoint92, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint92, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint92PositiveFacts : PositiveEndpointFacts 8
    endpoint92 :=
  { valid := endpoint92_valid
    positive := by
      norm_num [endpoint92] }

noncomputable def endpoint93 : EndpointCache :=
  { input := (11/4), certificate := { exponent := 1, mantissa := (11/8) }, enclosure := { lower := (472671419663311212421855887424/467250883900214061725454218985), upper := (7562742844867410654012289713199/7476014142403424987607267503760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint93_valid : endpoint93.Valid 8 := by
  constructor
  · norm_num [endpoint93, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint93, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint93PositiveFacts : PositiveEndpointFacts 8
    endpoint93 :=
  { valid := endpoint93_valid
    positive := by
      norm_num [endpoint93] }

noncomputable def endpoint94 : EndpointCache :=
  { input := (79/32), certificate := { exponent := 1, mantissa := (79/64) }, enclosure := { lower := (291124466913067724298522624770844209694784/322142987426645926085805568211574355329645), upper := (2943850666180307236471752785050064610249724013/3257509888858243604579665905755439881093370240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint94_valid : endpoint94.Valid 8 := by
  constructor
  · norm_num [endpoint94, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint94, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint94PositiveFacts : PositiveEndpointFacts 8
    endpoint94 :=
  { valid := endpoint94_valid
    positive := by
      norm_num [endpoint94] }

noncomputable def endpoint95 : EndpointCache :=
  { input := (169/64), certificate := { exponent := 1, mantissa := (169/128) }, enclosure := { lower := (467344964476279881516741243071708216000/481294996467513828750950674381324802127), upper := (1555324069684240779449047415027347372302395/1601749748243886022083163844341048941478656) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint95_valid : endpoint95.Valid 8 := by
  constructor
  · norm_num [endpoint95, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint95, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint95PositiveFacts : PositiveEndpointFacts 8
    endpoint95 :=
  { valid := endpoint95_valid
    positive := by
      norm_num [endpoint95] }

noncomputable def endpoint96 : EndpointCache :=
  { input := (45/16), certificate := { exponent := 1, mantissa := (45/32) }, enclosure := { lower := (11476139692697511350593811685036094784/11097989393282403274597131856194625089), upper := (524623537648396928271409660649359853863/507336657978624149695868884854611432640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint96_valid : endpoint96.Valid 8 := by
  constructor
  · norm_num [endpoint96, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint96, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint96PositiveFacts : PositiveEndpointFacts 8
    endpoint96 :=
  { valid := endpoint96_valid
    positive := by
      norm_num [endpoint96] }

noncomputable def endpoint97 : EndpointCache :=
  { input := (23/8), certificate := { exponent := 1, mantissa := (23/16) }, enclosure := { lower := (179170565962646738307668800/169660633889932869164850369), upper := (131869538724166933714088817145/124870226542990591705329871584) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint97_valid : endpoint97.Valid 8 := by
  constructor
  · norm_num [endpoint97, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint97, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint97PositiveFacts : PositiveEndpointFacts 8
    endpoint97 :=
  { valid := endpoint97_valid
    positive := by
      norm_num [endpoint97] }

noncomputable def endpoint98 : EndpointCache :=
  { input := (47/16), certificate := { exponent := 1, mantissa := (47/32) }, enclosure := { lower := (6763812130643048613283330003366366158784/6276976846331554026337130122369035727395), upper := (20345547217960405865191484752053890431178867/18881146353765314511222087408086059468004160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint98_valid : endpoint98.Valid 8 := by
  constructor
  · norm_num [endpoint98, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint98, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint98PositiveFacts : PositiveEndpointFacts 8
    endpoint98 :=
  { valid := endpoint98_valid
    positive := by
      norm_num [endpoint98] }

noncomputable def endpoint99 : EndpointCache :=
  { input := (3), certificate := { exponent := 1, mantissa := (3/2) }, enclosure := { lower := (7223350264060068616064/6574976764068603515625), upper := (14446700757266763145333/13149953528137207031250) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint99_valid : endpoint99.Valid 8 := by
  constructor
  · norm_num [endpoint99, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint99, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint99PositiveFacts : PositiveEndpointFacts 8
    endpoint99 :=
  { valid := endpoint99_valid
    positive := by
      norm_num [endpoint99] }

noncomputable def endpoint100 : EndpointCache :=
  { input := (81/64), certificate := { exponent := 0, mantissa := (81/64) }, enclosure := { lower := (2794340747653098780057303366408923008/11862237766588141422807241973876953125), upper := (3219080541296373934963524219218584011101/13665297907109538919073942753906250000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint100_valid : endpoint100.Valid 8 := by
  constructor
  · norm_num [endpoint100, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint100, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint100PositiveFacts : PositiveEndpointFacts 8
    endpoint100 :=
  { valid := endpoint100_valid
    positive := by
      norm_num [endpoint100] }

noncomputable def endpoint101 : EndpointCache :=
  { input := (151/128), certificate := { exponent := 0, mantissa := (151/128) }, enclosure := { lower := (11987503067717463681580203711705751728512/72541809686322587659571399473335721967985), upper := (463388918585686278193030698683052017242796417/2804176195234485948568392018041265668394428160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint101_valid : endpoint101.Valid 8 := by
  constructor
  · norm_num [endpoint101, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint101, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint101PositiveFacts : PositiveEndpointFacts 8
    endpoint101 :=
  { valid := endpoint101_valid
    positive := by
      norm_num [endpoint101] }

noncomputable def endpoint102 : EndpointCache :=
  { input := (313/256), certificate := { exponent := 0, mantissa := (313/256) }, enclosure := { lower := (213471430477760688044012144179232851289728896/1061910897788279919169436815554783082481040245), upper := (34210077562644020365410161025109941756955228082661/170177592835958586726417266313547317666081585502720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint102_valid : endpoint102.Valid 8 := by
  constructor
  · norm_num [endpoint102, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint102, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint102PositiveFacts : PositiveEndpointFacts 8
    endpoint102 :=
  { valid := endpoint102_valid
    positive := by
      norm_num [endpoint102] }

noncomputable def endpoint103 : EndpointCache :=
  { input := (341/256), certificate := { exponent := 0, mantissa := (341/256) }, enclosure := { lower := (375496260009725561591818378175528976337485440/1309695390894956243314492733139656202225195279), upper := (5959876638874536413230952084791629336043070856805/20787485244284745493887628660392623241718299468288) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint103_valid : endpoint103.Valid 8 := by
  constructor
  · norm_num [endpoint103, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint103, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint103PositiveFacts : PositiveEndpointFacts 8
    endpoint103 :=
  { valid := endpoint103_valid
    positive := by
      norm_num [endpoint103] }

noncomputable def endpoint104 : EndpointCache :=
  { input := (349/256), certificate := { exponent := 0, mantissa := (349/256) }, enclosure := { lower := (75085461371617884563441316745496027751470208/242293641123758402403083975463240203857421875), upper := (13416870921572981574091129413552587330264302321419/43294966145122141408602269407575465546875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint104_valid : endpoint104.Valid 8 := by
  constructor
  · norm_num [endpoint104, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint104, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint104PositiveFacts : PositiveEndpointFacts 8
    endpoint104 :=
  { valid := endpoint104_valid
    positive := by
      norm_num [endpoint104] }

noncomputable def endpoint105 : EndpointCache :=
  { input := (339/256), certificate := { exponent := 0, mantissa := (339/256) }, enclosure := { lower := (749437103228686629375719768154386855408361856/2668720164843641246370516513923845367431640625), upper := (6194204720628542395531938165353339770098257249653/22057353408170529707144657632796856796875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint105_valid : endpoint105.Valid 8 := by
  constructor
  · norm_num [endpoint105, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint105, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint105PositiveFacts : PositiveEndpointFacts 8
    endpoint105 :=
  { valid := endpoint105_valid
    positive := by
      norm_num [endpoint105] }

noncomputable def endpoint106 : EndpointCache :=
  { input := (347/256), certificate := { exponent := 0, mantissa := (347/256) }, enclosure := { lower := (25428904010531636873811098933510470422414976/83607189822861282733238982065299761827534655), upper := (4517800802127424771414527332664897516075395112679/14853987772688826935518170509649416885327116945920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint106_valid : endpoint106.Valid 8 := by
  constructor
  · norm_num [endpoint106, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint106, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint106PositiveFacts : PositiveEndpointFacts 8
    endpoint106 :=
  { valid := endpoint106_valid
    positive := by
      norm_num [endpoint106] }

noncomputable def endpoint107 : EndpointCache :=
  { input := (361/256), certificate := { exponent := 0, mantissa := (361/256) }, enclosure := { lower := (35139346411490189778165260313091763702037120/102238271387885379441998598806624487199081399), upper := (6494875675931832343272296870523718271010227698215/18896904177165630453023485014626017217980613139968) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint107_valid : endpoint107.Valid 8 := by
  constructor
  · norm_num [endpoint107, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint107, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint107PositiveFacts : PositiveEndpointFacts 8
    endpoint107 :=
  { valid := endpoint107_valid
    positive := by
      norm_num [endpoint107] }

noncomputable def endpoint108 : EndpointCache :=
  { input := (373/256), certificate := { exponent := 0, mantissa := (373/256) }, enclosure := { lower := (138315595568615654757912794361140205198648192/367468749272700023342044137650625608288430365), upper := (26414959179367485137902259976788033180093526938037/70177711861103159657770221231965876168491277386240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint108_valid : endpoint108.Valid 8 := by
  constructor
  · norm_num [endpoint108, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint108, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint108PositiveFacts : PositiveEndpointFacts 8
    endpoint108 :=
  { valid := endpoint108_valid
    positive := by
      norm_num [endpoint108] }

noncomputable def endpoint109 : EndpointCache :=
  { input := (369/256), certificate := { exponent := 0, mantissa := (369/256) }, enclosure := { lower := (14284855281486403286974503150785589526438993792/39070309487687637783892569132149219512939453125), upper := (99955894023120760332108372445135063985404659594943/273387978921846297453157603740692138671875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint109_valid : endpoint109.Valid 8 := by
  constructor
  · norm_num [endpoint109, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint109, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint109PositiveFacts : PositiveEndpointFacts 8
    endpoint109 :=
  { valid := endpoint109_valid
    positive := by
      norm_num [endpoint109] }

noncomputable def endpoint110 : EndpointCache :=
  { input := (191/128), certificate := { exponent := 0, mantissa := (191/128) }, enclosure := { lower := (937772570658561752246503768215012980352/2343007088464032252327418069173983031935), upper := (45853327615173210825637394215965445740172287/114563674597537321009801433910331074329493760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint110_valid : endpoint110.Valid 8 := by
  constructor
  · norm_num [endpoint110, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint110, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint110PositiveFacts : PositiveEndpointFacts 8
    endpoint110 :=
  { valid := endpoint110_valid
    positive := by
      norm_num [endpoint110] }

noncomputable def endpoint111 : EndpointCache :=
  { input := (379/256), certificate := { exponent := 0, mantissa := (379/256) }, enclosure := { lower := (2161191820526579910002452984576873714751695488/5508203301504962557904924296570608978271484375), upper := (419374950391231405902976498597734138359019493469439/1068855834250434974436334749900933531015625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint111_valid : endpoint111.Valid 8 := by
  constructor
  · norm_num [endpoint111, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint111, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint111PositiveFacts : PositiveEndpointFacts 8
    endpoint111 :=
  { valid := endpoint111_valid
    positive := by
      norm_num [endpoint111] }

noncomputable def endpoint112 : EndpointCache :=
  { input := (391/256), certificate := { exponent := 0, mantissa := (391/256) }, enclosure := { lower := (617849335875350457176681605038236683707530880/1458808507956892995457767475164214001324979343), upper := (123688494249202939955596111341083429517633246538335/292041792824906322546681386388074329353250264633856) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint112_valid : endpoint112.Valid 8 := by
  constructor
  · norm_num [endpoint112, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint112, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint112PositiveFacts : PositiveEndpointFacts 8
    endpoint112 :=
  { valid := endpoint112_valid
    positive := by
      norm_num [endpoint112] }

noncomputable def endpoint113 : EndpointCache :=
  { input := (199/128), certificate := { exponent := 0, mantissa := (199/128) }, enclosure := { lower := (346298426172456596117486413376474701740416/784768615578759928776703815919521711482145), upper := (17641827023374175403696780857083758083277231569/39979252352044345811600399198204114069746394880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint113_valid : endpoint113.Valid 8 := by
  constructor
  · norm_num [endpoint113, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint113, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint113PositiveFacts : PositiveEndpointFacts 8
    endpoint113 :=
  { valid := endpoint113_valid
    positive := by
      norm_num [endpoint113] }

noncomputable def endpoint114 : EndpointCache :=
  { input := (205/128), certificate := { exponent := 0, mantissa := (205/128) }, enclosure := { lower := (6305221049057202996748708933496673365632/13387457772260311515116018914215480921615), upper := (13235920027098023266633047756239483993677951/28102951355528845932531546904721137550654208) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint114_valid : endpoint114.Valid 8 := by
  constructor
  · norm_num [endpoint114, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint114, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint114PositiveFacts : PositiveEndpointFacts 8
    endpoint114 :=
  { valid := endpoint114_valid
    positive := by
      norm_num [endpoint114] }

noncomputable def endpoint115 : EndpointCache :=
  { input := (1325/1024), certificate := { exponent := 0, mantissa := (1325/1024) }, enclosure := { lower := (202199516318499050780897381017746461676218937534676864/784643801340290299275693875486830565604266855479921605), upper := (109737721496376391096371232913355322886454473877323520778409/425841883863402351222904580104212684564747707806063053465600) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint115_valid : endpoint115.Valid 8 := by
  constructor
  · norm_num [endpoint115, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint115, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint115PositiveFacts : PositiveEndpointFacts 8
    endpoint115 :=
  { valid := endpoint115_valid
    positive := by
      norm_num [endpoint115] }

noncomputable def endpoint116 : EndpointCache :=
  { input := (79/64), certificate := { exponent := 0, mantissa := (79/64) }, enclosure := { lower := (315155078906212326771989588807040/1496713245251111814466916391664649), upper := (3186848157899619738001236071870304105/15134764335979242667889458552512930688) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint116_valid : endpoint116.Valid 8 := by
  constructor
  · norm_num [endpoint116, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint116, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint116PositiveFacts : PositiveEndpointFacts 8
    endpoint116 :=
  { valid := endpoint116_valid
    positive := by
      norm_num [endpoint116] }

noncomputable def endpoint117 : EndpointCache :=
  { input := (317/256), certificate := { exponent := 0, mantissa := (317/256) }, enclosure := { lower := (756307886559230434695795082981376156613260416/3538707496196290725128874801818530259534090355), upper := (122751795220109370134294003850312694061913932432779/574346381462642769851316895834354735243421000977920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint117_valid : endpoint117.Valid 8 := by
  constructor
  · norm_num [endpoint117, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint117, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint117PositiveFacts : PositiveEndpointFacts 8
    endpoint117 :=
  { valid := endpoint117_valid
    positive := by
      norm_num [endpoint117] }

noncomputable def endpoint118 : EndpointCache :=
  { input := (325/256), certificate := { exponent := 0, mantissa := (325/256) }, enclosure := { lower := (49511416294946969799015808940594910745706112/207466522586652985938640720817674027444851215), upper := (18107032245009206150422367301861302642663967057/75873471117404520571845749327606501465545587200) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint118_valid : endpoint118.Valid 8 := by
  constructor
  · norm_num [endpoint118, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint118, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint118PositiveFacts : PositiveEndpointFacts 8
    endpoint118 :=
  { valid := endpoint118_valid
    positive := by
      norm_num [endpoint118] }

noncomputable def endpoint119 : EndpointCache :=
  { input := (91/64), certificate := { exponent := 0, mantissa := (91/64) }, enclosure := { lower := (1261517059832695769906017640751952512/3584095345128865145245506439208984375), upper := (161474183658703511715939413693397012621/458764204176494738591424824218750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint119_valid : endpoint119.Valid 8 := by
  constructor
  · norm_num [endpoint119, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint119, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint119PositiveFacts : PositiveEndpointFacts 8
    endpoint119 :=
  { valid := endpoint119_valid
    positive := by
      norm_num [endpoint119] }

noncomputable def endpoint120 : EndpointCache :=
  { input := (95/64), certificate := { exponent := 0, mantissa := (95/64) }, enclosure := { lower := (6224041635683481347022504276802008448/15757314433368697961247168503726900985), upper := (15136869258049944636631541118948069327269/38321788701952673441753113801063823195520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint120_valid : endpoint120.Valid 8 := by
  constructor
  · norm_num [endpoint120, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint120, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint120PositiveFacts : PositiveEndpointFacts 8
    endpoint120 :=
  { valid := endpoint120_valid
    positive := by
      norm_num [endpoint120] }

noncomputable def endpoint121 : EndpointCache :=
  { input := (389/256), certificate := { exponent := 0, mantissa := (389/256) }, enclosure := { lower := (1248580831302373539893130290367613979248941952/2984166261847499570324364685858249053955078125), upper := (248677347011565804872263805224100877820016621386021/594350426039642794422363065753015747578125000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint121_valid : endpoint121.Valid 8 := by
  constructor
  · norm_num [endpoint121, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint121, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint121PositiveFacts : PositiveEndpointFacts 8
    endpoint121 :=
  { valid := endpoint121_valid
    positive := by
      norm_num [endpoint121] }

noncomputable def endpoint122 : EndpointCache :=
  { input := (397/256), certificate := { exponent := 0, mantissa := (397/256) }, enclosure := { lower := (3675595209290388928519010390614645695192742272/8377256264660150434511194821997768657360830785), upper := (747116184638425416081422483257331293446106088020713/1702794617379880817920483504298554448369791908682240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint122_valid : endpoint122.Valid 8 := by
  constructor
  · norm_num [endpoint122, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint122, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint122PositiveFacts : PositiveEndpointFacts 8
    endpoint122 :=
  { valid := endpoint122_valid
    positive := by
      norm_num [endpoint122] }

noncomputable def endpoint123 : EndpointCache :=
  { input := (385/256), certificate := { exponent := 0, mantissa := (385/256) }, enclosure := { lower := (2588241630063285391504181096722285506315225984/6342705172639659631031273425309634421408693005), upper := (3442025232733153761872781569443209276587301645/8434974151666248652176654529242942399379872256) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint123_valid : endpoint123.Valid 8 := by
  constructor
  · norm_num [endpoint123, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint123, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint123PositiveFacts : PositiveEndpointFacts 8
    endpoint123 :=
  { valid := endpoint123_valid
    positive := by
      norm_num [endpoint123] }

noncomputable def endpoint124 : EndpointCache :=
  { input := (393/256), certificate := { exponent := 0, mantissa := (393/256) }, enclosure := { lower := (2679224576676554171379273124187251519210001024/6250638147377309888193600594335395600759859655), upper := (179700950809729773777794953434080538723235430663933/419242801820890928820921179063263653734165306780160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint124_valid : endpoint124.Valid 8 := by
  constructor
  · norm_num [endpoint124, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint124, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint124PositiveFacts : PositiveEndpointFacts 8
    endpoint124 :=
  { valid := endpoint124_valid
    positive := by
      norm_num [endpoint124] }

noncomputable def endpoint125 : EndpointCache :=
  { input := (797/512), certificate := { exponent := 0, mantissa := (797/512) }, enclosure := { lower := (326573409989888096834364338663640327831209189760/737968884197776317251355109301877964870958493937), upper := (38075100565035269909276085217421955788733467929316415/86039581360366112892244848949189008530600801962830848) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint125_valid : endpoint125.Valid 8 := by
  constructor
  · norm_num [endpoint125, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint125, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint125PositiveFacts : PositiveEndpointFacts 8
    endpoint125 :=
  { valid := endpoint125_valid
    positive := by
      norm_num [endpoint125] }

noncomputable def endpoint126 : EndpointCache :=
  { input := (417/256), certificate := { exponent := 0, mantissa := (417/256) }, enclosure := { lower := (8262531830999788694927541282265999010289806464/16934583297425323478563242890901763619218089795), upper := (588027865418975867006561444533660374749338877898497/1205200424111165421322388870059696713252513014530560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint126_valid : endpoint126.Valid 8 := by
  constructor
  · norm_num [endpoint126, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint126, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint126PositiveFacts : PositiveEndpointFacts 8
    endpoint126 :=
  { valid := endpoint126_valid
    positive := by
      norm_num [endpoint126] }

noncomputable def endpoint127 : EndpointCache :=
  { input := (403/256), certificate := { exponent := 0, mantissa := (403/256) }, enclosure := { lower := (622891816521763688497486985874592882991699328/1372736750723946278963309920181383183616607785), upper := (9886538912217810252641386783593339134179803545301/21788077707490475339705655053118913890362798763520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint127_valid : endpoint127.Valid 8 := by
  constructor
  · norm_num [endpoint127, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint127, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint127PositiveFacts : PositiveEndpointFacts 8
    endpoint127 :=
  { valid := endpoint127_valid
    positive := by
      norm_num [endpoint127] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
