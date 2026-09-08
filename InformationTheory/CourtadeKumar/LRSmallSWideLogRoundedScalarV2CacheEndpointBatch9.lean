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

noncomputable def endpoint576 : EndpointCache :=
  { input := (123/32), certificate := { exponent := 1, mantissa := (123/64) }, enclosure := { lower := (3465164918915189927937832770698440444112576/2573559289187143427122321785029220321246015), upper := (18185185821040125642563457673053016831815406253/13506039149654128705537944727833348245899086720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint576_valid : endpoint576.Valid 8 := by
  constructor
  · norm_num [endpoint576, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint576, EndpointCache.Valid,
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

theorem endpoint576PositiveFacts : PositiveEndpointFacts 8
    endpoint576 :=
  { valid := endpoint576_valid
    positive := by
      norm_num [endpoint576] }

noncomputable def endpoint577 : EndpointCache :=
  { input := (253/64), certificate := { exponent := 1, mantissa := (253/128) }, enclosure := { lower := (56504747035511211678503620658362980569792/41109118799358461871047370432658721145135), upper := (332699957969629706353607109492247625718223381/242050491490622623496726917107494550102554880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint577_valid : endpoint577.Valid 8 := by
  constructor
  · norm_num [endpoint577, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint577, EndpointCache.Valid,
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

theorem endpoint577PositiveFacts : PositiveEndpointFacts 8
    endpoint577 :=
  { valid := endpoint577_valid
    positive := by
      norm_num [endpoint577] }

noncomputable def endpoint578 : EndpointCache :=
  { input := (219/64), certificate := { exponent := 1, mantissa := (219/128) }, enclosure := { lower := (6749754685837897753733888208509514219114980632000/5486763929190619683812692668945127924505855713803), upper := (126139417384331301558949797461641759390491679757504305/102536644308714300651091600597246550653165431579550464) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint578_valid : endpoint578.Valid 8 := by
  constructor
  · norm_num [endpoint578, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint578, EndpointCache.Valid,
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

theorem endpoint578PositiveFacts : PositiveEndpointFacts 8
    endpoint578 :=
  { valid := endpoint578_valid
    positive := by
      norm_num [endpoint578] }

noncomputable def endpoint579 : EndpointCache :=
  { input := (1811/512), certificate := { exponent := 1, mantissa := (1811/1024) }, enclosure := { lower := (16643057783833349669146502154569524428823409241757901248/13174169443667218247537761095382097280994559783935546875), upper := (8818271986850963657693469086979883784989561544547844829446837/6980292275194538348629104740567618757743512947187500000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint579_valid : endpoint579.Valid 8 := by
  constructor
  · norm_num [endpoint579, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint579, EndpointCache.Valid,
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

theorem endpoint579PositiveFacts : PositiveEndpointFacts 8
    endpoint579 :=
  { valid := endpoint579_valid
    positive := by
      norm_num [endpoint579] }

noncomputable def endpoint580 : EndpointCache :=
  { input := (1889/512), certificate := { exponent := 1, mantissa := (1889/1024) }, enclosure := { lower := (2233146551417404962233502576581896401682896802332857536/1710596531408777283713045701596179895880355512009642455), upper := (8639311666416658784260283896832404061840255364835255894686487/6617736904358257231736715940485496470155246719357367495669760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint580_valid : endpoint580.Valid 8 := by
  constructor
  · norm_num [endpoint580, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint580, EndpointCache.Valid,
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

theorem endpoint580PositiveFacts : PositiveEndpointFacts 8
    endpoint580 :=
  { valid := endpoint580_valid
    positive := by
      norm_num [endpoint580] }

noncomputable def endpoint581 : EndpointCache :=
  { input := (125/32), certificate := { exponent := 1, mantissa := (125/64) }, enclosure := { lower := (8198712813888304175174319902391745856/6017060175107238586678655810836052721), upper := (18739915380189288587374366457158649443487/13753280400245116769551213281910977648000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint581_valid : endpoint581.Valid 8 := by
  constructor
  · norm_num [endpoint581, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint581, EndpointCache.Valid,
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

theorem endpoint581PositiveFacts : PositiveEndpointFacts 8
    endpoint581 :=
  { valid := endpoint581_valid
    positive := by
      norm_num [endpoint581] }

noncomputable def endpoint582 : EndpointCache :=
  { input := (65/16), certificate := { exponent := 2, mantissa := (65/64) }, enclosure := { lower := (319841888725485757581526999965908224/228165373492510687147573824727807245), upper := (40939762774541356542836613620027070989/29205167807041367954889449565159327360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint582_valid : endpoint582.Valid 8 := by
  constructor
  · norm_num [endpoint582, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint582, EndpointCache.Valid,
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

theorem endpoint582PositiveFacts : PositiveEndpointFacts 8
    endpoint582 :=
  { valid := endpoint582_valid
    positive := by
      norm_num [endpoint582] }

noncomputable def endpoint583 : EndpointCache :=
  { input := (33/8), certificate := { exponent := 2, mantissa := (33/32) }, enclosure := { lower := (5240747044974050141806232087403176704/3698308321052177846959803314208984375), upper := (335407819126066110760144659257937553591/236691732547339382205427412109375000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint583_valid : endpoint583.Valid 8 := by
  constructor
  · norm_num [endpoint583, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint583, EndpointCache.Valid,
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

theorem endpoint583PositiveFacts : PositiveEndpointFacts 8
    endpoint583 :=
  { valid := endpoint583_valid
    positive := by
      norm_num [endpoint583] }

noncomputable def endpoint584 : EndpointCache :=
  { input := (67/16), certificate := { exponent := 2, mantissa := (67/64) }, enclosure := { lower := (17716915675400598488095147720909277777334016/12371250253334335980866606473073327130615855), upper := (151940272529236362473949133593237480125515762151/106095842172595265371912017113076853472161572480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint584_valid : endpoint584.Valid 8 := by
  constructor
  · norm_num [endpoint584, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint584, EndpointCache.Valid,
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

theorem endpoint584PositiveFacts : PositiveEndpointFacts 8
    endpoint584 :=
  { valid := endpoint584_valid
    positive := by
      norm_num [endpoint584] }

noncomputable def endpoint585 : EndpointCache :=
  { input := (17/4), certificate := { exponent := 2, mantissa := (17/16) }, enclosure := { lower := (118382079185661094640435968/81816660605951299041818805), upper := (64399852627928335825040071237/44508263369637506678749429920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint585_valid : endpoint585.Valid 8 := by
  constructor
  · norm_num [endpoint585, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint585, EndpointCache.Valid,
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

theorem endpoint585PositiveFacts : PositiveEndpointFacts 8
    endpoint585 :=
  { valid := endpoint585_valid
    positive := by
      norm_num [endpoint585] }

noncomputable def endpoint586 : EndpointCache :=
  { input := (245/64), certificate := { exponent := 1, mantissa := (245/128) }, enclosure := { lower := (21771107699400301781085123372334352416598348543552/16218348567904969338751018392902538616849375631397), upper := (195069128406510815468448643549824032251831196443675291/145316403168428525275209124800406746006970405657317120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint586_valid : endpoint586.Valid 8 := by
  constructor
  · norm_num [endpoint586, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint586, EndpointCache.Valid,
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

theorem endpoint586PositiveFacts : PositiveEndpointFacts 8
    endpoint586 :=
  { valid := endpoint586_valid
    positive := by
      norm_num [endpoint586] }

noncomputable def endpoint587 : EndpointCache :=
  { input := (257/64), certificate := { exponent := 2, mantissa := (257/256) }, enclosure := { lower := (133740477803296233217475154896715779799595264/96202813458440477121243003089250057392711265), upper := (17598107472373992937737785478949902312231836216161/12658751006115431741521639318495879551962519093760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint587_valid : endpoint587.Valid 8 := by
  constructor
  · norm_num [endpoint587, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint587, EndpointCache.Valid,
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

theorem endpoint587PositiveFacts : PositiveEndpointFacts 8
    endpoint587 :=
  { valid := endpoint587_valid
    positive := by
      norm_num [endpoint587] }

noncomputable def endpoint588 : EndpointCache :=
  { input := (267/64), certificate := { exponent := 2, mantissa := (267/256) }, enclosure := { lower := (1418291539304283241841308285023086734172488831331072/992947160094592010626618662109760716813749225026595), upper := (64628710439674817925032201626492962022174333755924753881/45246616191190368740233759195017576343768924686011880960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint588_valid : endpoint588.Valid 8 := by
  constructor
  · norm_num [endpoint588, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint588, EndpointCache.Valid,
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

theorem endpoint588PositiveFacts : PositiveEndpointFacts 8
    endpoint588 :=
  { valid := endpoint588_valid
    positive := by
      norm_num [endpoint588] }

noncomputable def endpoint589 : EndpointCache :=
  { input := (69/16), certificate := { exponent := 2, mantissa := (69/64) }, enclosure := { lower := (3242088270985603707782063144312788588658432/2218302311891501659826218435801946376867855), upper := (1363529728192692310262563020479782757315608859/932954572315511555218341010714418590499852160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint589_valid : endpoint589.Valid 8 := by
  constructor
  · norm_num [endpoint589, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint589, EndpointCache.Valid,
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

theorem endpoint589PositiveFacts : PositiveEndpointFacts 8
    endpoint589 :=
  { valid := endpoint589_valid
    positive := by
      norm_num [endpoint589] }

noncomputable def endpoint590 : EndpointCache :=
  { input := (35/8), certificate := { exponent := 2, mantissa := (35/32) }, enclosure := { lower := (5472540836945885412983013945148861696/3707918334255063210374730502641315105), upper := (350242621833695195102267616471949848547/237306773392324045463982752169044166720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint590_valid : endpoint590.Valid 8 := by
  constructor
  · norm_num [endpoint590, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint590, EndpointCache.Valid,
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

theorem endpoint590PositiveFacts : PositiveEndpointFacts 8
    endpoint590 :=
  { valid := endpoint590_valid
    positive := by
      norm_num [endpoint590] }

noncomputable def endpoint591 : EndpointCache :=
  { input := (71/16), certificate := { exponent := 2, mantissa := (71/64) }, enclosure := { lower := (2017180216277146562889667374790779136/1353729409450096679233540191650390625), upper := (18332134234224617605111169316844243701073/12302692873082478620874413261718750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint591_valid : endpoint591.Valid 8 := by
  constructor
  · norm_num [endpoint591, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint591, EndpointCache.Valid,
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

theorem endpoint591PositiveFacts : PositiveEndpointFacts 8
    endpoint591 :=
  { valid := endpoint591_valid
    positive := by
      norm_num [endpoint591] }

noncomputable def endpoint592 : EndpointCache :=
  { input := (9/2), certificate := { exponent := 2, mantissa := (9/8) }, enclosure := { lower := (927573135741079430077794009088/616705722043969904359337088765), upper := (14841170515691527828627715960413/9867291552703518469749393420240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint592_valid : endpoint592.Valid 8 := by
  constructor
  · norm_num [endpoint592, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint592, EndpointCache.Valid,
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

theorem endpoint592PositiveFacts : PositiveEndpointFacts 8
    endpoint592 :=
  { valid := endpoint592_valid
    positive := by
      norm_num [endpoint592] }

noncomputable def endpoint593 : EndpointCache :=
  { input := (249/64), certificate := { exponent := 1, mantissa := (249/128) }, enclosure := { lower := (1988991896738920074800060868476040221560841243200/1464033632873383902617252548654113221501501360181), upper := (42262100646164834794868579842526865870392584527163895/31107786631293661162811382153802597730463900901125888) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint593_valid : endpoint593.Valid 8 := by
  constructor
  · norm_num [endpoint593, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint593, EndpointCache.Valid,
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

theorem endpoint593PositiveFacts : PositiveEndpointFacts 8
    endpoint593 :=
  { valid := endpoint593_valid
    positive := by
      norm_num [endpoint593] }

noncomputable def endpoint594 : EndpointCache :=
  { input := (133/32), certificate := { exponent := 2, mantissa := (133/128) }, enclosure := { lower := (38004053237868019992575652046226208862976/26676751706125469370369907811142019243515), upper := (184851719470439672500707568248473978852373029/129755720298594283017479231593394781600456960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint594_valid : endpoint594.Valid 8 := by
  constructor
  · norm_num [endpoint594, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint594, EndpointCache.Valid,
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

theorem endpoint594PositiveFacts : PositiveEndpointFacts 8
    endpoint594 :=
  { valid := endpoint594_valid
    positive := by
      norm_num [endpoint594] }

noncomputable def endpoint595 : EndpointCache :=
  { input := (139/32), certificate := { exponent := 2, mantissa := (139/128) }, enclosure := { lower := (2623730971885811959927762939975482984704/1786384584124349015115713813464760735745), upper := (93362845118621356877578872155211568828720121/63566709041480835353877560338330046020750080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint595_valid : endpoint595.Valid 8 := by
  constructor
  · norm_num [endpoint595, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint595, EndpointCache.Valid,
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

theorem endpoint595PositiveFacts : PositiveEndpointFacts 8
    endpoint595 :=
  { valid := endpoint595_valid
    positive := by
      norm_num [endpoint595] }

noncomputable def endpoint596 : EndpointCache :=
  { input := (135/32), certificate := { exponent := 2, mantissa := (135/128) }, enclosure := { lower := (617879493447229781988228877078109271249058915072/429220429383383962872949152760009543936539380235), upper := (158177154151368867727295625621739560212231322438733/109880429922146294495474983106562443247754081340160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint596_valid : endpoint596.Valid 8 := by
  constructor
  · norm_num [endpoint596, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint596, EndpointCache.Valid,
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

theorem endpoint596PositiveFacts : PositiveEndpointFacts 8
    endpoint596 :=
  { valid := endpoint596_valid
    positive := by
      norm_num [endpoint596] }

noncomputable def endpoint597 : EndpointCache :=
  { input := (141/32), certificate := { exponent := 2, mantissa := (141/128) }, enclosure := { lower := (892845948959554329464013208786946162553424029952/602044173024888399530098224472319208702660614145), upper := (10742722710297638940413579778999115529846479602145379/7243795489835457223146141836850944719110412509392640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint597_valid : endpoint597.Valid 8 := by
  constructor
  · norm_num [endpoint597, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint597, EndpointCache.Valid,
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

theorem endpoint597PositiveFacts : PositiveEndpointFacts 8
    endpoint597 :=
  { valid := endpoint597_valid
    positive := by
      norm_num [endpoint597] }

noncomputable def endpoint598 : EndpointCache :=
  { input := (73/16), certificate := { exponent := 2, mantissa := (73/64) }, enclosure := { lower := (5251573004651021074061147989362809933431552/3459828921021475143154639076638107624241395), upper := (49070699281978444373753946308382408829324679843/32328641438024663737636947532106477640911594880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint598_valid : endpoint598.Valid 8 := by
  constructor
  · norm_num [endpoint598, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint598, EndpointCache.Valid,
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

theorem endpoint598PositiveFacts : PositiveEndpointFacts 8
    endpoint598 :=
  { valid := endpoint598_valid
    positive := by
      norm_num [endpoint598] }

noncomputable def endpoint599 : EndpointCache :=
  { input := (277/64), certificate := { exponent := 2, mantissa := (277/256) }, enclosure := { lower := (1932797752320214309907269493069538288211880611132672/1319194829413154084493506064807126419068719963718845), upper := (274117114944495487812091452713026245603752305540734979733/187093487486691164879207004135205897258002140134461473280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint599_valid : endpoint599.Valid 8 := by
  constructor
  · norm_num [endpoint599, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint599, EndpointCache.Valid,
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

theorem endpoint599PositiveFacts : PositiveEndpointFacts 8
    endpoint599 :=
  { valid := endpoint599_valid
    positive := by
      norm_num [endpoint599] }

noncomputable def endpoint600 : EndpointCache :=
  { input := (289/64), certificate := { exponent := 2, mantissa := (289/256) }, enclosure := { lower := (36104519837601619420847706658281828624460658972501248/23949237535972898217062494382309622542790069580078125), upper := (5342313714814233486604188376644752033131945690816098565229/3543720779722837803382303168761590228411561015625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint600_valid : endpoint600.Valid 8 := by
  constructor
  · norm_num [endpoint600, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint600, EndpointCache.Valid,
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

theorem endpoint600PositiveFacts : PositiveEndpointFacts 8
    endpoint600 :=
  { valid := endpoint600_valid
    positive := by
      norm_num [endpoint600] }

noncomputable def endpoint601 : EndpointCache :=
  { input := (37/8), certificate := { exponent := 2, mantissa := (37/32) }, enclosure := { lower := (29325859044756953706015451467008/19148750603991267233119152752745), upper := (69443635798043540922808471204199009/45344241430251320808026153718500160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint601_valid : endpoint601.Valid 8 := by
  constructor
  · norm_num [endpoint601, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint601, EndpointCache.Valid,
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

theorem endpoint601PositiveFacts : PositiveEndpointFacts 8
    endpoint601 :=
  { valid := endpoint601_valid
    positive := by
      norm_num [endpoint601] }

noncomputable def endpoint602 : EndpointCache :=
  { input := (75/16), certificate := { exponent := 2, mantissa := (75/64) }, enclosure := { lower := (46501435806105155273994877371021952686581504/30099976819839504143838172300900154501741895), upper := (29760919587177423465840578859391149437999093057/19263985164697282652056430272576098881114812800) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint602_valid : endpoint602.Valid 8 := by
  constructor
  · norm_num [endpoint602, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint602, EndpointCache.Valid,
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

theorem endpoint602PositiveFacts : PositiveEndpointFacts 8
    endpoint602 :=
  { valid := endpoint602_valid
    positive := by
      norm_num [endpoint602] }

noncomputable def endpoint603 : EndpointCache :=
  { input := (19/4), certificate := { exponent := 2, mantissa := (19/16) }, enclosure := { lower := (6948235758425277443494326753028864/4459300944837382767811431884765625), upper := (603503919371225586918753371404999751/387322139208732674689907226562500000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint603_valid : endpoint603.Valid 8 := by
  constructor
  · norm_num [endpoint603, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint603, EndpointCache.Valid,
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

theorem endpoint603PositiveFacts : PositiveEndpointFacts 8
    endpoint603 :=
  { valid := endpoint603_valid
    positive := by
      norm_num [endpoint603] }

noncomputable def endpoint604 : EndpointCache :=
  { input := (77/16), certificate := { exponent := 2, mantissa := (77/64) }, enclosure := { lower := (4083646234120914050813255587547525888/2599034391871790436009650046544216515), upper := (47518793596352021035933534741940019989/30243309287235379619021382359787246720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint604_valid : endpoint604.Valid 8 := by
  constructor
  · norm_num [endpoint604, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint604, EndpointCache.Valid,
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

theorem endpoint604PositiveFacts : PositiveEndpointFacts 8
    endpoint604 :=
  { valid := endpoint604_valid
    positive := by
      norm_num [endpoint604] }

noncomputable def endpoint605 : EndpointCache :=
  { input := (39/8), certificate := { exponent := 2, mantissa := (39/32) }, enclosure := { lower := (2004506612750900684861072945875135790848/1265375402837569342575662652464584721355), upper := (128288426038015644481778055269567160367117/80984025781604437924842409757733422166720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint605_valid : endpoint605.Valid 8 := by
  constructor
  · norm_num [endpoint605, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint605, EndpointCache.Valid,
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

theorem endpoint605PositiveFacts : PositiveEndpointFacts 8
    endpoint605 :=
  { valid := endpoint605_valid
    positive := by
      norm_num [endpoint605] }

noncomputable def endpoint606 : EndpointCache :=
  { input := (79/16), certificate := { exponent := 2, mantissa := (79/64) }, enclosure := { lower := (514416970059091912610471917320281550810368/322142987426645926085805568211574355329645), upper := (5201784514748270088604344035895444575533999501/3257509888858243604579665905755439881093370240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint606_valid : endpoint606.Valid 8 := by
  constructor
  · norm_num [endpoint606, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint606, EndpointCache.Valid,
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

theorem endpoint606PositiveFacts : PositiveEndpointFacts 8
    endpoint606 :=
  { valid := endpoint606_valid
    positive := by
      norm_num [endpoint606] }

noncomputable def endpoint607 : EndpointCache :=
  { input := (5), certificate := { exponent := 2, mantissa := (5/4) }, enclosure := { lower := (710786490865530496/441636478343022105), upper := (5686292050037866457/3533091826744176840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint607_valid : endpoint607.Valid 8 := by
  constructor
  · norm_num [endpoint607, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint607, EndpointCache.Valid,
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

theorem endpoint607PositiveFacts : PositiveEndpointFacts 8
    endpoint607 :=
  { valid := endpoint607_valid
    positive := by
      norm_num [endpoint607] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
