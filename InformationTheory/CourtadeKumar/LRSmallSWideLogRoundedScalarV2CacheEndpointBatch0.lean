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

noncomputable def endpoint0 : EndpointCache :=
  { input := (15/16), certificate := { exponent := -1, mantissa := (15/8) }, enclosure := { lower := (-14829988367038102440469002133361/229785007247895206797429833032940), upper := (-11863986822541712719068146439055/183828005798316165437943866426352) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint0_valid : endpoint0.Valid 8 := by
  constructor
  · norm_num [endpoint0, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint0, EndpointCache.Valid,
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

theorem endpoint0PositiveFacts : PositiveEndpointFacts 8
    endpoint0 :=
  { valid := endpoint0_valid
    positive := by
      norm_num [endpoint0] }

noncomputable def endpoint1 : EndpointCache :=
  { input := (9/8), certificate := { exponent := 0, mantissa := (9/8) }, enclosure := { lower := (15186690954718839083648/128937846355259652395685), upper := (80995685091833808447791/687668513894718146110320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint1_valid : endpoint1.Valid 8 := by
  constructor
  · norm_num [endpoint1, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint1, EndpointCache.Valid,
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

theorem endpoint1PositiveFacts : PositiveEndpointFacts 8
    endpoint1 :=
  { valid := endpoint1_valid
    positive := by
      norm_num [endpoint1] }

noncomputable def endpoint2 : EndpointCache :=
  { input := (17/16), certificate := { exponent := 0, mantissa := (17/16) }, enclosure := { lower := (4960104107519400271158656/81816660605951299041818805), upper := (2698296634490553747510310229/44508263369637506678749429920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint2_valid : endpoint2.Valid 8 := by
  constructor
  · norm_num [endpoint2, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint2, EndpointCache.Valid,
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

theorem endpoint2PositiveFacts : PositiveEndpointFacts 8
    endpoint2 :=
  { valid := endpoint2_valid
    positive := by
      norm_num [endpoint2] }

noncomputable def endpoint3 : EndpointCache :=
  { input := (1), certificate := { exponent := 0, mantissa := (1) }, enclosure := { lower := (0), upper := (0) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint3_valid : endpoint3.Valid 8 := by
  constructor
  · norm_num [endpoint3, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint3, EndpointCache.Valid,
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

theorem endpoint3PositiveFacts : PositiveEndpointFacts 8
    endpoint3 :=
  { valid := endpoint3_valid
    positive := by
      norm_num [endpoint3] }

noncomputable def endpoint4 : EndpointCache :=
  { input := (19/16), certificate := { exponent := 0, mantissa := (19/16) }, enclosure := { lower := (17802331868287910996928384/103592116687293853759765625), upper := (1546259682274149996923953431/8997715277982094726562500000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint4_valid : endpoint4.Valid 8 := by
  constructor
  · norm_num [endpoint4, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint4, EndpointCache.Valid,
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

theorem endpoint4PositiveFacts : PositiveEndpointFacts 8
    endpoint4 :=
  { valid := endpoint4_valid
    positive := by
      norm_num [endpoint4] }

noncomputable def endpoint5 : EndpointCache :=
  { input := (5/4), certificate := { exponent := 0, mantissa := (5/4) }, enclosure := { lower := (689838325171541248/3091455348401154735), upper := (5518706601372332987/24731642787209237880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint5_valid : endpoint5.Valid 8 := by
  constructor
  · norm_num [endpoint5, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint5, EndpointCache.Valid,
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

theorem endpoint5PositiveFacts : PositiveEndpointFacts 8
    endpoint5 :=
  { valid := endpoint5_valid
    positive := by
      norm_num [endpoint5] }

noncomputable def endpoint6 : EndpointCache :=
  { input := (21/16), certificate := { exponent := 0, mantissa := (21/16) }, enclosure := { lower := (816893620567644072196837760/3004017427977904101560233437), upper := (3734370836880705373046314135/13732651099327561607132495712) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint6_valid : endpoint6.Valid 8 := by
  constructor
  · norm_num [endpoint6, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint6, EndpointCache.Valid,
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

theorem endpoint6PositiveFacts : PositiveEndpointFacts 8
    endpoint6 :=
  { valid := endpoint6_valid
    positive := by
      norm_num [endpoint6] }

noncomputable def endpoint7 : EndpointCache :=
  { input := (11/8), certificate := { exponent := 0, mantissa := (11/8) }, enclosure := { lower := (24196605158966360095104/75981540784523365486495), upper := (387145682543520520295829/1215704652552373847783920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint7_valid : endpoint7.Valid 8 := by
  constructor
  · norm_num [endpoint7, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint7, EndpointCache.Valid,
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

theorem endpoint7PositiveFacts : PositiveEndpointFacts 8
    endpoint7 :=
  { valid := endpoint7_valid
    positive := by
      norm_num [endpoint7] }

noncomputable def endpoint8 : EndpointCache :=
  { input := (75/64), certificate := { exponent := 0, mantissa := (75/64) }, enclosure := { lower := (90738765585422444357953777967352704/572105219389111357094462233906485405), upper := (58072809974670364527077456679412930043/366147340409031268540455829700150659200) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint8_valid : endpoint8.Valid 8 := by
  constructor
  · norm_num [endpoint8, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint8, EndpointCache.Valid,
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

theorem endpoint8PositiveFacts : PositiveEndpointFacts 8
    endpoint8 :=
  { valid := endpoint8_valid
    positive := by
      norm_num [endpoint8] }

noncomputable def endpoint9 : EndpointCache :=
  { input := (85/64), certificate := { exponent := 0, mantissa := (85/64) }, enclosure := { lower := (80364408442587281743428103101161088/283204446629708069656541379253045535), upper := (174872952771074221071476349030067475451/616252875866244759572634041254627084160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint9_valid : endpoint9.Valid 8 := by
  constructor
  · norm_num [endpoint9, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint9, EndpointCache.Valid,
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

theorem endpoint9PositiveFacts : PositiveEndpointFacts 8
    endpoint9 :=
  { valid := endpoint9_valid
    positive := by
      norm_num [endpoint9] }

noncomputable def endpoint10 : EndpointCache :=
  { input := (23/16), certificate := { exponent := 0, mantissa := (23/16) }, enclosure := { lower := (43979125786766431735831168/121186167064237763689178835), upper := (32368636579098477792379628803/89193018959278994075235622560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint10_valid : endpoint10.Valid 8 := by
  constructor
  · norm_num [endpoint10, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint10, EndpointCache.Valid,
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

theorem endpoint10PositiveFacts : PositiveEndpointFacts 8
    endpoint10 :=
  { valid := endpoint10_valid
    positive := by
      norm_num [endpoint10] }

noncomputable def endpoint11 : EndpointCache :=
  { input := (3/2), certificate := { exponent := 0, mantissa := (3/2) }, enclosure := { lower := (557378411704256/1374664306640625), upper := (2229513646832039/5498657226562500) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint11_valid : endpoint11.Valid 8 := by
  constructor
  · norm_num [endpoint11, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint11, EndpointCache.Valid,
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

theorem endpoint11PositiveFacts : PositiveEndpointFacts 8
    endpoint11 :=
  { valid := endpoint11_valid
    positive := by
      norm_num [endpoint11] }

noncomputable def endpoint12 : EndpointCache :=
  { input := (37/32), certificate := { exponent := 0, mantissa := (37/32) }, enclosure := { lower := (1668032459219097129547269642880/11489250362394760339871491651647), upper := (3949900863430822005059041692074215/27206544858150792484815692231100096) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint12_valid : endpoint12.Valid 8 := by
  constructor
  · norm_num [endpoint12, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint12, EndpointCache.Valid,
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

theorem endpoint12PositiveFacts : PositiveEndpointFacts 8
    endpoint12 :=
  { valid := endpoint12_valid
    positive := by
      norm_num [endpoint12] }

noncomputable def endpoint13 : EndpointCache :=
  { input := (25/16), certificate := { exponent := 0, mantissa := (25/16) }, enclosure := { lower := (3473571708099948161728128384/7783267066532647243997448005), upper := (555771473312685564757866777009/1245322730645223559039591680800) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint13_valid : endpoint13.Valid 8 := by
  constructor
  · norm_num [endpoint13, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint13, EndpointCache.Valid,
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

theorem endpoint13PositiveFacts : PositiveEndpointFacts 8
    endpoint13 :=
  { valid := endpoint13_valid
    positive := by
      norm_num [endpoint13] }

noncomputable def endpoint14 : EndpointCache :=
  { input := (13/8), certificate := { exponent := 0, mantissa := (13/8) }, enclosure := { lower := (14188710865320259162240/29224474672086271707129), upper := (32431339124328735506995/66798799250482906759152) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint14_valid : endpoint14.Valid 8 := by
  constructor
  · norm_num [endpoint14, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint14, EndpointCache.Valid,
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

theorem endpoint14PositiveFacts : PositiveEndpointFacts 8
    endpoint14 :=
  { valid := endpoint14_valid
    positive := by
      norm_num [endpoint14] }

noncomputable def endpoint15 : EndpointCache :=
  { input := (27/16), certificate := { exponent := 0, mantissa := (27/16) }, enclosure := { lower := (6807512322206387759364138368/13010103147942628435539087165), upper := (653521183161791622866135949133/1248969902202492329811752367840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint15_valid : endpoint15.Valid 8 := by
  constructor
  · norm_num [endpoint15, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint15, EndpointCache.Valid,
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

theorem endpoint15PositiveFacts : PositiveEndpointFacts 8
    endpoint15 :=
  { valid := endpoint15_valid
    positive := by
      norm_num [endpoint15] }

noncomputable def endpoint16 : EndpointCache :=
  { input := (7/4), certificate := { exponent := 0, mantissa := (7/4) }, enclosure := { lower := (1063632581645643264/1900647917084121205), upper := (8509060661559256707/15205183336672969640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint16_valid : endpoint16.Valid 8 := by
  constructor
  · norm_num [endpoint16, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint16, EndpointCache.Valid,
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

theorem endpoint16PositiveFacts : PositiveEndpointFacts 8
    endpoint16 :=
  { valid := endpoint16_valid
    positive := by
      norm_num [endpoint16] }

noncomputable def endpoint17 : EndpointCache :=
  { input := (175/128), certificate := { exponent := 0, mantissa := (175/128) }, enclosure := { lower := (78229402184110140169986328523204387886464/250129413090926262462271931068967016996105), upper := (100133634795672411382343987290687085715336643/320165648756385615951708071768277781755014400) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint17_valid : endpoint17.Valid 8 := by
  constructor
  · norm_num [endpoint17, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint17, EndpointCache.Valid,
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

theorem endpoint17PositiveFacts : PositiveEndpointFacts 8
    endpoint17 :=
  { valid := endpoint17_valid
    positive := by
      norm_num [endpoint17] }

noncomputable def endpoint18 : EndpointCache :=
  { input := (193/128), certificate := { exponent := 0, mantissa := (193/128) }, enclosure := { lower := (3755517494798387184610942732623875543680/9145079094179730162385783613331237461031), upper := (185552608384523254786740711297246159414875815/451840067885232107863156796767469780474619648) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint18_valid : endpoint18.Valid 8 := by
  constructor
  · norm_num [endpoint18, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint18, EndpointCache.Valid,
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

theorem endpoint18PositiveFacts : PositiveEndpointFacts 8
    endpoint18 :=
  { valid := endpoint18_valid
    positive := by
      norm_num [endpoint18] }

noncomputable def endpoint19 : EndpointCache :=
  { input := (49/32), certificate := { exponent := 0, mantissa := (49/32) }, enclosure := { lower := (271204098768733795660454784130688/636503241502371295767130914513015), upper := (121499436250167170817629935649707889/285153452193062340503674649701830720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint19_valid : endpoint19.Valid 8 := by
  constructor
  · norm_num [endpoint19, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint19, EndpointCache.Valid,
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

theorem endpoint19PositiveFacts : PositiveEndpointFacts 8
    endpoint19 :=
  { valid := endpoint19_valid
    positive := by
      norm_num [endpoint19] }

noncomputable def endpoint20 : EndpointCache :=
  { input := (109/64), certificate := { exponent := 0, mantissa := (109/64) }, enclosure := { lower := (1983428394967116018286664190507250560/3724994401942853020867780256890885357), upper := (27672792979317606252631018803809943016245/51971121895906685347147270144141632500864) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint20_valid : endpoint20.Valid 8 := by
  constructor
  · norm_num [endpoint20, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint20, EndpointCache.Valid,
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

theorem endpoint20PositiveFacts : PositiveEndpointFacts 8
    endpoint20 :=
  { valid := endpoint20_valid
    positive := by
      norm_num [endpoint20] }

noncomputable def endpoint21 : EndpointCache :=
  { input := (29/16), certificate := { exponent := 0, mantissa := (29/16) }, enclosure := { lower := (4315914374033892725365299328/7257210008829333343505859375), upper := (4005168549094682836024443088999/6734690888193621342773437500000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint21_valid : endpoint21.Valid 8 := by
  constructor
  · norm_num [endpoint21, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint21, EndpointCache.Valid,
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

theorem endpoint21PositiveFacts : PositiveEndpointFacts 8
    endpoint21 :=
  { valid := endpoint21_valid
    positive := by
      norm_num [endpoint21] }

noncomputable def endpoint22 : EndpointCache :=
  { input := (15/8), certificate := { exponent := 0, mantissa := (15/8) }, enclosure := { lower := (1078565316952419459529856/1715797740213357665481045), upper := (17257045171037201852989499/27452763843413722647696720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint22_valid : endpoint22.Valid 8 := by
  constructor
  · norm_num [endpoint22, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint22, EndpointCache.Valid,
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

theorem endpoint22PositiveFacts : PositiveEndpointFacts 8
    endpoint22 :=
  { valid := endpoint22_valid
    positive := by
      norm_num [endpoint22] }

noncomputable def endpoint23 : EndpointCache :=
  { input := (31/16), certificate := { exponent := 0, mantissa := (31/16) }, enclosure := { lower := (7986658964539861241868808320/12075411699171188606954058343), upper := (7922765791448193812962910587815/11978808405577819098098425876256) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint23_valid : endpoint23.Valid 8 := by
  constructor
  · norm_num [endpoint23, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint23, EndpointCache.Valid,
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

theorem endpoint23PositiveFacts : PositiveEndpointFacts 8
    endpoint23 :=
  { valid := endpoint23_valid
    positive := by
      norm_num [endpoint23] }

noncomputable def endpoint24 : EndpointCache :=
  { input := (2), certificate := { exponent := 1, mantissa := (1) }, enclosure := { lower := (149337754816/215448838605), upper := (597351034279/861795354420) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint24_valid : endpoint24.Valid 8 := by
  constructor
  · norm_num [endpoint24, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint24, EndpointCache.Valid,
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

theorem endpoint24PositiveFacts : PositiveEndpointFacts 8
    endpoint24 :=
  { valid := endpoint24_valid
    positive := by
      norm_num [endpoint24] }

noncomputable def endpoint25 : EndpointCache :=
  { input := (71/64), certificate := { exponent := 0, mantissa := (71/64) }, enclosure := { lower := (20073253173352124187401700862968448/193389915635728097033362884521484375), upper := (182425724839424104615605649895159814439/1757527553297496945839201894531250000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint25_valid : endpoint25.Valid 8 := by
  constructor
  · norm_num [endpoint25, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint25, EndpointCache.Valid,
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

theorem endpoint25PositiveFacts : PositiveEndpointFacts 8
    endpoint25 :=
  { valid := endpoint25_valid
    positive := by
      norm_num [endpoint25] }

noncomputable def endpoint26 : EndpointCache :=
  { input := (77/64), certificate := { exponent := 0, mantissa := (77/64) }, enclosure := { lower := (36970732120868757063772637234218624/199925722451676187385357695888016655), upper := (4732253711471201033919136356700052867/25590492473814551985325785073666131840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint26_valid : endpoint26.Valid 8 := by
  constructor
  · norm_num [endpoint26, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint26, EndpointCache.Valid,
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

theorem endpoint26PositiveFacts : PositiveEndpointFacts 8
    endpoint26 :=
  { valid := endpoint26_valid
    positive := by
      norm_num [endpoint26] }

noncomputable def endpoint27 : EndpointCache :=
  { input := (39/32), certificate := { exponent := 0, mantissa := (39/32) }, enclosure := { lower := (7476642038441543133773158036352/37794080348645649732136272095685), upper := (478505090460258798945516922215683/2418821142313321582856721414123840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint27_valid : endpoint27.Valid 8 := by
  constructor
  · norm_num [endpoint27, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint27, EndpointCache.Valid,
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

theorem endpoint27PositiveFacts : PositiveEndpointFacts 8
    endpoint27 :=
  { valid := endpoint27_valid
    positive := by
      norm_num [endpoint27] }

noncomputable def endpoint28 : EndpointCache :=
  { input := (41/32), certificate := { exponent := 0, mantissa := (41/32) }, enclosure := { lower := (11051256574059117567660227910528/44590976554632012370764723109285), upper := (28998497250331207966834844868403317/117006722479354400460886633438763840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint28_valid : endpoint28.Valid 8 := by
  constructor
  · norm_num [endpoint28, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint28, EndpointCache.Valid,
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

theorem endpoint28PositiveFacts : PositiveEndpointFacts 8
    endpoint28 :=
  { valid := endpoint28_valid
    positive := by
      norm_num [endpoint28] }

noncomputable def endpoint29 : EndpointCache :=
  { input := (83/64), certificate := { exponent := 0, mantissa := (83/64) }, enclosure := { lower := (180339022073847432515403941065693312/693724955507504299499293577587418235), upper := (273703110073223839781923059754659226549/1052876275330246525411499281184104475520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint29_valid : endpoint29.Valid 8 := by
  constructor
  · norm_num [endpoint29, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint29, EndpointCache.Valid,
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

theorem endpoint29PositiveFacts : PositiveEndpointFacts 8
    endpoint29 :=
  { valid := endpoint29_valid
    positive := by
      norm_num [endpoint29] }

noncomputable def endpoint30 : EndpointCache :=
  { input := (87/64), certificate := { exponent := 0, mantissa := (87/64) }, enclosure := { lower := (6690746731676291497865050179630660736/21792186181982035341968159767342083795), upper := (24836051867984511906419069621267438088577/80892595107517315189385809056373815047040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint30_valid : endpoint30.Valid 8 := by
  constructor
  · norm_num [endpoint30, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint30, EndpointCache.Valid,
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

theorem endpoint30PositiveFacts : PositiveEndpointFacts 8
    endpoint30 :=
  { valid := endpoint30_valid
    positive := by
      norm_num [endpoint30] }

noncomputable def endpoint31 : EndpointCache :=
  { input := (73/64), certificate := { exponent := 0, mantissa := (73/64) }, enclosure := { lower := (74027051119655807832145918909024128/562616661258596816284391871252324965), upper := (691708765662063868467040760692752629877/5257090082800328651361357644981724472960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint31_valid : endpoint31.Valid 8 := by
  constructor
  · norm_num [endpoint31, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint31, EndpointCache.Valid,
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

theorem endpoint31PositiveFacts : PositiveEndpointFacts 8
    endpoint31 :=
  { valid := endpoint31_valid
    positive := by
      norm_num [endpoint31] }

noncomputable def endpoint32 : EndpointCache :=
  { input := (303/256), certificate := { exponent := 0, mantissa := (303/256) }, enclosure := { lower := (94977979705148500958222950063820402763584128/563482402012434174128570241683860203744782535), upper := (4911501286512639312329991859241614090127594980621/29138801972866996012536624337955778856050194449920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint32_valid : endpoint32.Valid 8 := by
  constructor
  · norm_num [endpoint32, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint32, EndpointCache.Valid,
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

theorem endpoint32PositiveFacts : PositiveEndpointFacts 8
    endpoint32 :=
  { valid := endpoint32_valid
    positive := by
      norm_num [endpoint32] }

noncomputable def endpoint33 : EndpointCache :=
  { input := (319/256), certificate := { exponent := 0, mantissa := (319/256) }, enclosure := { lower := (39063698067461951851857550902724862994163584/177551240992769357384187169373035430908203125), upper := (580017788905675313271768708149624089908393776127/2636280826260639418440411090850830078125000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint33_valid : endpoint33.Valid 8 := by
  constructor
  · norm_num [endpoint33, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint33, EndpointCache.Valid,
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

theorem endpoint33PositiveFacts : PositiveEndpointFacts 8
    endpoint33 :=
  { valid := endpoint33_valid
    positive := by
      norm_num [endpoint33] }

noncomputable def endpoint34 : EndpointCache :=
  { input := (89/64), certificate := { exponent := 0, mantissa := (89/64) }, enclosure := { lower := (583600865034722795306871289097321600/1769810610395354813690204493667945971), upper := (6648381054477310060193109151635701339075/20161682473623882037558809591865240501632) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint34_valid : endpoint34.Valid 8 := by
  constructor
  · norm_num [endpoint34, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint34, EndpointCache.Valid,
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

theorem endpoint34PositiveFacts : PositiveEndpointFacts 8
    endpoint34 :=
  { valid := endpoint34_valid
    positive := by
      norm_num [endpoint34] }

noncomputable def endpoint35 : EndpointCache :=
  { input := (1323/1024), certificate := { exponent := 0, mantissa := (1323/1024) }, enclosure := { lower := (320592891323188579089127700971618650036571221130981504/1251409890014415386617668399885229819838185950129595995), upper := (13788059070027761517248124634341746929507233325320379604477/53820636549739976947652682542263964091600701343173664552960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint35_valid : endpoint35.Valid 8 := by
  constructor
  · norm_num [endpoint35, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint35, EndpointCache.Valid,
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

theorem endpoint35PositiveFacts : PositiveEndpointFacts 8
    endpoint35 :=
  { valid := endpoint35_valid
    positive := by
      norm_num [endpoint35] }

noncomputable def endpoint36 : EndpointCache :=
  { input := (1365/1024), certificate := { exponent := 0, mantissa := (1365/1024) }, enclosure := { lower := (554677036653569523914184927286073976015504052004146304/1929728239582455264551186994676677442656292083295129155), upper := (227195714213308915728959633799517093348987696276166194547/790416686932973676360166193019567080512017237317684901888) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint36_valid : endpoint36.Valid 8 := by
  constructor
  · norm_num [endpoint36, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint36, EndpointCache.Valid,
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

theorem endpoint36PositiveFacts : PositiveEndpointFacts 8
    endpoint36 :=
  { valid := endpoint36_valid
    positive := by
      norm_num [endpoint36] }

noncomputable def endpoint37 : EndpointCache :=
  { input := (43/32), certificate := { exponent := 0, mantissa := (43/32) }, enclosure := { lower := (5389599427353695030772742767232/18241124278865754604339599609375), upper := (14832177624078058659880489631419879/50199574015438556671142578125000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint37_valid : endpoint37.Valid 8 := by
  constructor
  · norm_num [endpoint37, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint37, EndpointCache.Valid,
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

theorem endpoint37PositiveFacts : PositiveEndpointFacts 8
    endpoint37 :=
  { valid := endpoint37_valid
    positive := by
      norm_num [endpoint37] }

noncomputable def endpoint38 : EndpointCache :=
  { input := (45/32), certificate := { exponent := 0, mantissa := (45/32) }, enclosure := { lower := (304252574731423713678996788608/892428418196892033009134305185), upper := (556347565223421945467862165967/1631869107560031146073845586624) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint38_valid : endpoint38.Valid 8 := by
  constructor
  · norm_num [endpoint38, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint38, EndpointCache.Valid,
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

theorem endpoint38PositiveFacts : PositiveEndpointFacts 8
    endpoint38 :=
  { valid := endpoint38_valid
    positive := by
      norm_num [endpoint38] }

noncomputable def endpoint39 : EndpointCache :=
  { input := (353/256), certificate := { exponent := 0, mantissa := (353/256) }, enclosure := { lower := (405120968671954523989333139286923730583705984/1260917539974174984360460915069948383614127105), upper := (10459991913415307616625269376038762215613063828727/32556170357824641424767466278011741580126125207040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint39_valid : endpoint39.Valid 8 := by
  constructor
  · norm_num [endpoint39, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint39, EndpointCache.Valid,
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

theorem endpoint39PositiveFacts : PositiveEndpointFacts 8
    endpoint39 :=
  { valid := endpoint39_valid
    positive := by
      norm_num [endpoint39] }

noncomputable def endpoint40 : EndpointCache :=
  { input := (365/256), certificate := { exponent := 0, mantissa := (365/256) }, enclosure := { lower := (4195511382386600700636896924858199538975898752/11827673820161567473975739110473236538703684515), upper := (156811433428211546618317612383381643262935351870559/442071136702358745907317224993047688870588912432640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint40_valid : endpoint40.Valid 8 := by
  constructor
  · norm_num [endpoint40, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint40, EndpointCache.Valid,
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

theorem endpoint40PositiveFacts : PositiveEndpointFacts 8
    endpoint40 :=
  { valid := endpoint40_valid
    positive := by
      norm_num [endpoint40] }

noncomputable def endpoint41 : EndpointCache :=
  { input := (93/64), certificate := { exponent := 0, mantissa := (93/64) }, enclosure := { lower := (14611121272626967690747316718126957952/39096814829990425252103275338893656185), upper := (57976929209892773870152354785347063360171/155136161245402007400345796544730027742080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint41_valid : endpoint41.Valid 8 := by
  constructor
  · norm_num [endpoint41, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint41, EndpointCache.Valid,
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

theorem endpoint41PositiveFacts : PositiveEndpointFacts 8
    endpoint41 :=
  { valid := endpoint41_valid
    positive := by
      norm_num [endpoint41] }

noncomputable def endpoint42 : EndpointCache :=
  { input := (47/32), certificate := { exponent := 0, mantissa := (47/32) }, enclosure := { lower := (11210811311359661505892250455680/29163553927053138501941321488199), upper := (33722120424668486461184918423419815/87723970212575840613839495036502592) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint42_valid : endpoint42.Valid 8 := by
  constructor
  · norm_num [endpoint42, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint42, EndpointCache.Valid,
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

theorem endpoint42PositiveFacts : PositiveEndpointFacts 8
    endpoint42 :=
  { valid := endpoint42_valid
    positive := by
      norm_num [endpoint42] }

noncomputable def endpoint43 : EndpointCache :=
  { input := (99/64), certificate := { exponent := 0, mantissa := (99/64) }, enclosure := { lower := (855292923568043476362214494415909760/1960616318271948327550385523012538509), upper := (12164166024335204881882676790997409295/27884320970978820658494371882844992128) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint43_valid : endpoint43.Valid 8 := by
  constructor
  · norm_num [endpoint43, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint43, EndpointCache.Valid,
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

theorem endpoint43PositiveFacts : PositiveEndpointFacts 8
    endpoint43 :=
  { valid := endpoint43_valid
    positive := by
      norm_num [endpoint43] }

noncomputable def endpoint44 : EndpointCache :=
  { input := (51/32), certificate := { exponent := 0, mantissa := (51/32) }, enclosure := { lower := (1283179788721283797223584186996352/2753074582727431237715512819561815), upper := (1396099610211044780048898400273905061/2995345146007445186634477947683254720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint44_valid : endpoint44.Valid 8 := by
  constructor
  · norm_num [endpoint44, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint44, EndpointCache.Valid,
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

theorem endpoint44PositiveFacts : PositiveEndpointFacts 8
    endpoint44 :=
  { valid := endpoint44_valid
    positive := by
      norm_num [endpoint44] }

noncomputable def endpoint45 : EndpointCache :=
  { input := (105/64), certificate := { exponent := 0, mantissa := (105/64) }, enclosure := { lower := (4494452478062520155142199992909513088/9078284905247059287718610714766514785), upper := (575289917278268548685727181623141038537/1162020467871623588827982171490113892480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint45_valid : endpoint45.Valid 8 := by
  constructor
  · norm_num [endpoint45, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint45, EndpointCache.Valid,
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

theorem endpoint45PositiveFacts : PositiveEndpointFacts 8
    endpoint45 :=
  { valid := endpoint45_valid
    positive := by
      norm_num [endpoint45] }

noncomputable def endpoint46 : EndpointCache :=
  { input := (103/64), certificate := { exponent := 0, mantissa := (103/64) }, enclosure := { lower := (401489445473367944066181281527587456/843738364387084090854464493590764055), upper := (5293236849550972681479513838992608705319/11123846596079316653825259883500633301120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint46_valid : endpoint46.Valid 8 := by
  constructor
  · norm_num [endpoint46, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint46, EndpointCache.Valid,
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

theorem endpoint46PositiveFacts : PositiveEndpointFacts 8
    endpoint46 :=
  { valid := endpoint46_valid
    positive := by
      norm_num [endpoint46] }

noncomputable def endpoint47 : EndpointCache :=
  { input := (101/64), certificate := { exponent := 0, mantissa := (101/64) }, enclosure := { lower := (1139154762292509252603734448320878976/2496846331968728608453943023681640625), upper := (14726992767540665656888616935018983943433/32279229379691723450092575410156250000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint47_valid : endpoint47.Valid 8 := by
  constructor
  · norm_num [endpoint47, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint47, EndpointCache.Valid,
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

theorem endpoint47PositiveFacts : PositiveEndpointFacts 8
    endpoint47 :=
  { valid := endpoint47_valid
    positive := by
      norm_num [endpoint47] }

noncomputable def endpoint48 : EndpointCache :=
  { input := (53/32), certificate := { exponent := 0, mantissa := (53/32) }, enclosure := { lower := (31513693862794562534258451434112/62458266657394967407073974609375), upper := (106894449604079145000188076969247719/211858440501883729444794921875000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint48_valid : endpoint48.Valid 8 := by
  constructor
  · norm_num [endpoint48, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint48, EndpointCache.Valid,
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

theorem endpoint48PositiveFacts : PositiveEndpointFacts 8
    endpoint48 :=
  { valid := endpoint48_valid
    positive := by
      norm_num [endpoint48] }

noncomputable def endpoint49 : EndpointCache :=
  { input := (97/64), certificate := { exponent := 0, mantissa := (97/64) }, enclosure := { lower := (34214887553724075391010668164538752/82281366770546621912213166562076065), upper := (60687434838754414044560806389154535511/145943635689015265380291239433533774720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint49_valid : endpoint49.Valid 8 := by
  constructor
  · norm_num [endpoint49, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint49, EndpointCache.Valid,
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

theorem endpoint49PositiveFacts : PositiveEndpointFacts 8
    endpoint49 :=
  { valid := endpoint49_valid
    positive := by
      norm_num [endpoint49] }

noncomputable def endpoint50 : EndpointCache :=
  { input := (1527/1024), certificate := { exponent := 0, mantissa := (1527/1024) }, enclosure := { lower := (22694282197365945987666887375938258634600402051816772736/56794132511324652747219279425947437845441703777131703795), upper := (23657245979691395861159605077998565945342222103765084030708897/59204021142045180412589287890549239528099486151802956250429440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint50_valid : endpoint50.Valid 8 := by
  constructor
  · norm_num [endpoint50, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint50, EndpointCache.Valid,
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

theorem endpoint50PositiveFacts : PositiveEndpointFacts 8
    endpoint50 :=
  { valid := endpoint50_valid
    positive := by
      norm_num [endpoint50] }

noncomputable def endpoint51 : EndpointCache :=
  { input := (1575/1024), certificate := { exponent := 0, mantissa := (1575/1024) }, enclosure := { lower := (32340968767261349509807500797838571762225811541592534144/75117440865154402366914485771679448278203599017415709955), upper := (331171520182443611703065892809429621696472954925167613991753/769202594459181080237204334301997550368804853938336869939200) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint51_valid : endpoint51.Valid 8 := by
  constructor
  · norm_num [endpoint51, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint51, EndpointCache.Valid,
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

theorem endpoint51PositiveFacts : PositiveEndpointFacts 8
    endpoint51 :=
  { valid := endpoint51_valid
    positive := by
      norm_num [endpoint51] }

noncomputable def endpoint52 : EndpointCache :=
  { input := (401/256), certificate := { exponent := 0, mantissa := (401/256) }, enclosure := { lower := (2472140924392354672753545729671466513273034880/5508531986423481726224470731310655182914429579), upper := (507560197485470025841877025744609616939830866579435/1130967719196577880174598534786853236914527365723648) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint52_valid : endpoint52.Valid 8 := by
  constructor
  · norm_num [endpoint52, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint52, EndpointCache.Valid,
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

theorem endpoint52PositiveFacts : PositiveEndpointFacts 8
    endpoint52 :=
  { valid := endpoint52_valid
    positive := by
      norm_num [endpoint52] }

noncomputable def endpoint53 : EndpointCache :=
  { input := (395/256), certificate := { exponent := 0, mantissa := (395/256) }, enclosure := { lower := (1487098990943091143373168105115613167162231936/3428799773772668413639567228160378598406603395), upper := (8592882855260593066576281761884159045576958872217/19812584749936698856413316463518713364050042017280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint53_valid : endpoint53.Valid 8 := by
  constructor
  · norm_num [endpoint53, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint53, EndpointCache.Valid,
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

theorem endpoint53PositiveFacts : PositiveEndpointFacts 8
    endpoint53 :=
  { valid := endpoint53_valid
    positive := by
      norm_num [endpoint53] }

noncomputable def endpoint54 : EndpointCache :=
  { input := (409/256), certificate := { exponent := 0, mantissa := (409/256) }, enclosure := { lower := (736843528157657978748262095321737645673696384/1572645082723420871645805380574775848388671875), upper := (22042989936329001123685454082776824217492179565781/47046351640420873984229259019343237265625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint54_valid : endpoint54.Valid 8 := by
  constructor
  · norm_num [endpoint54, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint54, EndpointCache.Valid,
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

theorem endpoint54PositiveFacts : PositiveEndpointFacts 8
    endpoint54 :=
  { valid := endpoint54_valid
    positive := by
      norm_num [endpoint54] }

noncomputable def endpoint55 : EndpointCache :=
  { input := (415/256), certificate := { exponent := 0, mantissa := (415/256) }, enclosure := { lower := (553206410143885746007768349488961232175734144/1145115252097234271308504964405058168992095705), upper := (23509059607888875730164269556599803594920118085253/48662817753124067593526226967357351949488099079680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint55_valid : endpoint55.Valid 8 := by
  constructor
  · norm_num [endpoint55, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint55, EndpointCache.Valid,
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

theorem endpoint55PositiveFacts : PositiveEndpointFacts 8
    endpoint55 :=
  { valid := endpoint55_valid
    positive := by
      norm_num [endpoint55] }

noncomputable def endpoint56 : EndpointCache :=
  { input := (429/256), certificate := { exponent := 0, mantissa := (429/256) }, enclosure := { lower := (79779263539766810488765654281686582290086827392/154527281229473002519516810341519918365478515625), upper := (40846982944054875234836929124554138032016131273269/79117967989490177289992606894858198203125000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint56_valid : endpoint56.Valid 8 := by
  constructor
  · norm_num [endpoint56, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint56, EndpointCache.Valid,
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

theorem endpoint56PositiveFacts : PositiveEndpointFacts 8
    endpoint56 :=
  { valid := endpoint56_valid
    positive := by
      norm_num [endpoint56] }

noncomputable def endpoint57 : EndpointCache :=
  { input := (411/256), certificate := { exponent := 0, mantissa := (411/256) }, enclosure := { lower := (9813113372330800325010578831888615929040428160/20728319574204898401292832245672008721873836387), upper := (688331024440436392397574632652709051047809302620665/1453967248213028393460284425040417379787118379529728) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint57_valid : endpoint57.Valid 8 := by
  constructor
  · norm_num [endpoint57, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint57, EndpointCache.Valid,
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

theorem endpoint57PositiveFacts : PositiveEndpointFacts 8
    endpoint57 :=
  { valid := endpoint57_valid
    positive := by
      norm_num [endpoint57] }

noncomputable def endpoint58 : EndpointCache :=
  { input := (431/256), certificate := { exponent := 0, mantissa := (431/256) }, enclosure := { lower := (800918370670956668404641236888278874384489600/1537476010317381063392910908584275513758715747), upper := (176740258750791716877485883202992519401444352683075/339277906148757114021040436019109246172163321321984) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint58_valid : endpoint58.Valid 8 := by
  constructor
  · norm_num [endpoint58, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint58, EndpointCache.Valid,
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

theorem endpoint58PositiveFacts : PositiveEndpointFacts 8
    endpoint58 :=
  { valid := endpoint58_valid
    positive := by
      norm_num [endpoint58] }

noncomputable def endpoint59 : EndpointCache :=
  { input := (215/128), certificate := { exponent := 0, mantissa := (215/128) }, enclosure := { lower := (39678647191720499243296774433484820032384/76509936662872593849794754775230516137005), upper := (62397506917211045317745211888321826906163679/120317340397843073299791522937962503090878720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint59_valid : endpoint59.Valid 8 := by
  constructor
  · norm_num [endpoint59, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint59, EndpointCache.Valid,
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

theorem endpoint59PositiveFacts : PositiveEndpointFacts 8
    endpoint59 :=
  { valid := endpoint59_valid
    positive := by
      norm_num [endpoint59] }

noncomputable def endpoint60 : EndpointCache :=
  { input := (451/256), certificate := { exponent := 0, mantissa := (451/256) }, enclosure := { lower := (34333865709674112440205225407599445910936960/60629486794286713862448252632095297147318873), upper := (102962358547110133060518699368346813710468190885/181819169540809528200073388464706353959502540288) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint60_valid : endpoint60.Valid 8 := by
  constructor
  · norm_num [endpoint60, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint60, EndpointCache.Valid,
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

theorem endpoint60PositiveFacts : PositiveEndpointFacts 8
    endpoint60 :=
  { valid := endpoint60_valid
    positive := by
      norm_num [endpoint60] }

noncomputable def endpoint61 : EndpointCache :=
  { input := (59/32), certificate := { exponent := 0, mantissa := (59/32) }, enclosure := { lower := (8177002694013895041745626512256/13365449653916666332298794326805), upper := (4410908898721376520969594693909963/7209705413312761724394321054002240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint61_valid : endpoint61.Valid 8 := by
  constructor
  · norm_num [endpoint61, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint61, EndpointCache.Valid,
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

theorem endpoint61PositiveFacts : PositiveEndpointFacts 8
    endpoint61 :=
  { valid := endpoint61_valid
    positive := by
      norm_num [endpoint61] }

noncomputable def endpoint62 : EndpointCache :=
  { input := (55/32), certificate := { exponent := 0, mantissa := (55/32) }, enclosure := { lower := (1006909880150923891225063513367936/1859148693773363321009043254036145), upper := (64442232368165789838465055372374023/118985516401495252544578768258313280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint62_valid : endpoint62.Valid 8 := by
  constructor
  · norm_num [endpoint62, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint62, EndpointCache.Valid,
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

theorem endpoint62PositiveFacts : PositiveEndpointFacts 8
    endpoint62 :=
  { valid := endpoint62_valid
    positive := by
      norm_num [endpoint62] }

noncomputable def endpoint63 : EndpointCache :=
  { input := (113/64), certificate := { exponent := 0, mantissa := (113/64) }, enclosure := { lower := (6393819597132809224028169167621552512/11246730589912266842519045826152087985), upper := (92480206769009823317750718370396608054673/162672711252491027610195478829463800615040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint63_valid : endpoint63.Valid 8 := by
  constructor
  · norm_num [endpoint63, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint63, EndpointCache.Valid,
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

theorem endpoint63PositiveFacts : PositiveEndpointFacts 8
    endpoint63 :=
  { valid := endpoint63_valid
    positive := by
      norm_num [endpoint63] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
