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

noncomputable def endpoint512 : EndpointCache :=
  { input := (2673/1024), certificate := { exponent := 1, mantissa := (2673/2048) }, enclosure := { lower := (2666197473077023454461449137630699001759863515830482295540909079616/2778779996018144355710778280871548156503230456834635047070076632605), upper := (10920745048029262005886587953592594673536010688221043411929378049468621/11381882863690319280991347838449861249037231951194665152799033887150080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint512_valid : endpoint512.Valid 8 := by
  constructor
  · norm_num [endpoint512, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint512, EndpointCache.Valid,
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

theorem endpoint512PositiveFacts : PositiveEndpointFacts 8
    endpoint512 :=
  { valid := endpoint512_valid
    positive := by
      norm_num [endpoint512] }

noncomputable def endpoint513 : EndpointCache :=
  { input := (2733/1024), certificate := { exponent := 1, mantissa := (2733/2048) }, enclosure := { lower := (470975928368261557309321089415943050268474838413809284455757649088/479763575803822893118806810434678287484838354179315667709120461015), upper := (251060854993736545768285948014999926762161481737349576305436096420599219/255745239073518536780790055091048986272146426533218932023886256996741120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint513_valid : endpoint513.Valid 8 := by
  constructor
  · norm_num [endpoint513, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint513, EndpointCache.Valid,
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

theorem endpoint513PositiveFacts : PositiveEndpointFacts 8
    endpoint513 :=
  { valid := endpoint513_valid
    positive := by
      norm_num [endpoint513] }

noncomputable def endpoint514 : EndpointCache :=
  { input := (345/128), certificate := { exponent := 1, mantissa := (345/256) }, enclosure := { lower := (2942334949296939808095290232468086934514181327169728/2967516845891753249450480079744113214311907819008103), upper := (173244684858869736559032752251238271115794690503415386749/174727391886106431327644267095333386058685132383197104640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint514_valid : endpoint514.Valid 8 := by
  constructor
  · norm_num [endpoint514, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint514, EndpointCache.Valid,
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

theorem endpoint514PositiveFacts : PositiveEndpointFacts 8
    endpoint514 :=
  { valid := endpoint514_valid
    positive := by
      norm_num [endpoint514] }

noncomputable def endpoint515 : EndpointCache :=
  { input := (349/128), certificate := { exponent := 1, mantissa := (349/256) }, enclosure := { lower := (804743930227486214547483425265149975075211423737536/802303597656042647665483494718226677802581787109375), upper := (143798085902279952588764519867411218365341726034309693623/143362025257962948626049914704210488603187734375000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint515_valid : endpoint515.Valid 8 := by
  constructor
  · norm_num [endpoint515, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint515, EndpointCache.Valid,
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

theorem endpoint515PositiveFacts : PositiveEndpointFacts 8
    endpoint515 :=
  { valid := endpoint515_valid
    positive := by
      norm_num [endpoint515] }

noncomputable def endpoint516 : EndpointCache :=
  { input := (723/256), certificate := { exponent := 1, mantissa := (723/512) }, enclosure := { lower := (408036943718779693865592663301480560137600260543905864128/393011418922752704621613406484393974974170277557373046875), upper := (100696990808544643217822900919681467028753022340713337668051697/96988930007432603457340242905844682720025637776718750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint516_valid : endpoint516.Valid 8 := by
  constructor
  · norm_num [endpoint516, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint516, EndpointCache.Valid,
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

theorem endpoint516PositiveFacts : PositiveEndpointFacts 8
    endpoint516 :=
  { valid := endpoint516_valid
    positive := by
      norm_num [endpoint516] }

noncomputable def endpoint517 : EndpointCache :=
  { input := (373/128), certificate := { exponent := 1, mantissa := (373/256) }, enclosure := { lower := (6283999436559983808043459614968247236601751951038400/5875377755431180590842285723449056813166158367173747), upper := (1200093095946872961360416883930547045145382615101554017755/1122056142221225144516696358321407073951220260329373507072) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint517_valid : endpoint517.Valid 8 := by
  constructor
  · norm_num [endpoint517, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint517, EndpointCache.Valid,
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

theorem endpoint517PositiveFacts : PositiveEndpointFacts 8
    endpoint517 :=
  { valid := endpoint517_valid
    positive := by
      norm_num [endpoint517] }

noncomputable def endpoint518 : EndpointCache :=
  { input := (357/128), certificate := { exponent := 1, mantissa := (357/256) }, enclosure := { lower := (143309165314908810203135281899405679394180463552111424/139717650886050848137411116379029901926891528438878985), upper := (178194713727022166591724846401557371844119236443726284283/173728919044598083169718050994725180910237694790286097920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint518_valid : endpoint518.Valid 8 := by
  constructor
  · norm_num [endpoint518, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint518, EndpointCache.Valid,
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

theorem endpoint518PositiveFacts : PositiveEndpointFacts 8
    endpoint518 :=
  { valid := endpoint518_valid
    positive := by
      norm_num [endpoint518] }

noncomputable def endpoint519 : EndpointCache :=
  { input := (713/256), certificate := { exponent := 1, mantissa := (713/512) }, enclosure := { lower := (661784065356137817104605738848625223831450220265843337152/646081711638257186393526920664513702504336833953857421875), upper := (69025213677707096231564863870678153514463815153404742576211077/67387430092518747267450103871458489766120910644531250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint519_valid : endpoint519.Valid 8 := by
  constructor
  · norm_num [endpoint519, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint519, EndpointCache.Valid,
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

theorem endpoint519PositiveFacts : PositiveEndpointFacts 8
    endpoint519 :=
  { valid := endpoint519_valid
    positive := by
      norm_num [endpoint519] }

noncomputable def endpoint520 : EndpointCache :=
  { input := (729/256), certificate := { exponent := 1, mantissa := (729/512) }, enclosure := { lower := (522716111290161686185156485871156345831820783401906347712/499491606443920962815766093848712476826008616065603321055), upper := (535261306872736298299420400895628300363460290646970131444743/511479404998575065923344480101081576269832822851177800760320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint520_valid : endpoint520.Valid 8 := by
  constructor
  · norm_num [endpoint520, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint520, EndpointCache.Valid,
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

theorem endpoint520PositiveFacts : PositiveEndpointFacts 8
    endpoint520 :=
  { valid := endpoint520_valid
    positive := by
      norm_num [endpoint520] }

noncomputable def endpoint521 : EndpointCache :=
  { input := (1443/512), certificate := { exponent := 1, mantissa := (1443/1024) }, enclosure := { lower := (24333694900569896325343274885839991573126017582432124277391168/23484610391835455751762490222072314745155981188308706959097145), upper := (1843910095791203301999493119535905948735125750086742610743371051223/1779569837051723495045554459067751722128939630525280578532545259520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint521_valid : endpoint521.Valid 8 := by
  constructor
  · norm_num [endpoint521, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint521, EndpointCache.Valid,
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

theorem endpoint521PositiveFacts : PositiveEndpointFacts 8
    endpoint521 :=
  { valid := endpoint521_valid
    positive := by
      norm_num [endpoint521] }

noncomputable def endpoint522 : EndpointCache :=
  { input := (2949/1024), certificate := { exponent := 1, mantissa := (2949/2048) }, enclosure := { lower := (17902205583832815041976796490548061999391981545253951275265416000/16924804837107941256561804637643547817404957273423161780756083689), upper := (72080868879491602413283092235326815590126494369452041981992307695383275/68145492602376627221300240215259576338469163007078269052859311170711552) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint522_valid : endpoint522.Valid 8 := by
  constructor
  · norm_num [endpoint522, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint522, EndpointCache.Valid,
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

theorem endpoint522PositiveFacts : PositiveEndpointFacts 8
    endpoint522 :=
  { valid := endpoint522_valid
    positive := by
      norm_num [endpoint522] }

noncomputable def endpoint523 : EndpointCache :=
  { input := (745/256), certificate := { exponent := 1, mantissa := (745/512) }, enclosure := { lower := (99137925011815438991854117769144618273191369509824/92807804189223926521476961073929200435880560552579), upper := (75630341466631206864547357427357947753843764055066848179/70801217659875149064704344064079108428524562034351467520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint523_valid : endpoint523.Valid 8 := by
  constructor
  · norm_num [endpoint523, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint523, EndpointCache.Valid,
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

theorem endpoint523PositiveFacts : PositiveEndpointFacts 8
    endpoint523 :=
  { valid := endpoint523_valid
    positive := by
      norm_num [endpoint523] }

noncomputable def endpoint524 : EndpointCache :=
  { input := (737/256), certificate := { exponent := 1, mantissa := (737/512) }, enclosure := { lower := (492131288559963708355277872420754696835667926419220943168/465411789808520705077505322773701245870133370234483293665), upper := (33764144001867701928444684677130721830975053984453772785731459/31930972075182988533957485184858095076658110265047429811768320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint524_valid : endpoint524.Valid 8 := by
  constructor
  · norm_num [endpoint524, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint524, EndpointCache.Valid,
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

theorem endpoint524PositiveFacts : PositiveEndpointFacts 8
    endpoint524 :=
  { valid := endpoint524_valid
    positive := by
      norm_num [endpoint524] }

noncomputable def endpoint525 : EndpointCache :=
  { input := (753/256), certificate := { exponent := 1, mantissa := (753/512) }, enclosure := { lower := (102609504369960117791456568268326686020522625002815860032/95106744234697649051223855406861029212935266265869140625), upper := (26373105677112306921596348403212186353391458449404112179168123/24444715830178928549741760212093049172425473876718750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint525_valid : endpoint525.Valid 8 := by
  constructor
  · norm_num [endpoint525, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint525, EndpointCache.Valid,
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

theorem endpoint525PositiveFacts : PositiveEndpointFacts 8
    endpoint525 :=
  { valid := endpoint525_valid
    positive := by
      norm_num [endpoint525] }

noncomputable def endpoint526 : EndpointCache :=
  { input := (97/32), certificate := { exponent := 1, mantissa := (97/64) }, enclosure := { lower := (664726030875935172917797215796760987416000/599405745039604707083427590904098354756331), upper := (1179034075578832302424415384220174672694198685/1063174532915961720449690995523612167522086528) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint526_valid : endpoint526.Valid 8 := by
  constructor
  · norm_num [endpoint526, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint526, EndpointCache.Valid,
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

theorem endpoint526PositiveFacts : PositiveEndpointFacts 8
    endpoint526 :=
  { valid := endpoint526_valid
    positive := by
      norm_num [endpoint526] }

noncomputable def endpoint527 : EndpointCache :=
  { input := (197/64), certificate := { exponent := 1, mantissa := (197/128) }, enclosure := { lower := (126894665362248224636267217207771300941801346496/112863413118047419645990091376006603240966796875), upper := (6399551862762084408936025456550519859599510474914067/5691927650369367467586572288274765014648437500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint527_valid : endpoint527.Valid 8 := by
  constructor
  · norm_num [endpoint527, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint527, EndpointCache.Valid,
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

theorem endpoint527PositiveFacts : PositiveEndpointFacts 8
    endpoint527 :=
  { valid := endpoint527_valid
    positive := by
      norm_num [endpoint527] }

noncomputable def endpoint528 : EndpointCache :=
  { input := (201/64), certificate := { exponent := 1, mantissa := (201/128) }, enclosure := { lower := (2017301064096590945691860138818366220462400165824/1762725091695517738349834356384354398152473901235), upper := (4942964054091603860256600355404758159304187807414679/4319180110394502892596622697243492376730176050568960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint528_valid : endpoint528.Valid 8 := by
  constructor
  · norm_num [endpoint528, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint528, EndpointCache.Valid,
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

theorem endpoint528PositiveFacts : PositiveEndpointFacts 8
    endpoint528 :=
  { valid := endpoint528_valid
    positive := by
      norm_num [endpoint528] }

noncomputable def endpoint529 : EndpointCache :=
  { input := (769/256), certificate := { exponent := 1, mantissa := (769/512) }, enclosure := { lower := (3586402433075624200131765427751908671901904283584/3260622180539071692746032942768005803935713667635), upper := (403447737011778173905560582716699033459764938777689717/366799499971225034126145730997188968334857334551598080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint529_valid : endpoint529.Valid 8 := by
  constructor
  · norm_num [endpoint529, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint529, EndpointCache.Valid,
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

theorem endpoint529PositiveFacts : PositiveEndpointFacts 8
    endpoint529 :=
  { valid := endpoint529_valid
    positive := by
      norm_num [endpoint529] }

noncomputable def endpoint530 : EndpointCache :=
  { input := (99/32), certificate := { exponent := 1, mantissa := (99/64) }, enclosure := { lower := (370680579701752012295824875096913300060050112/328214847491610184709636896311621540494862735), upper := (4313374084924902781217523930876324423614548711/3819227316266009422075774793444323380303857280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint530_valid : endpoint530.Valid 8 := by
  constructor
  · norm_num [endpoint530, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint530, EndpointCache.Valid,
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

theorem endpoint530PositiveFacts : PositiveEndpointFacts 8
    endpoint530 :=
  { valid := endpoint530_valid
    positive := by
      norm_num [endpoint530] }

noncomputable def endpoint531 : EndpointCache :=
  { input := (813/256), certificate := { exponent := 1, mantissa := (813/512) }, enclosure := { lower := (16957914856400392409051895900751464455188753460896721056064/14675142647110575773983419410630037062801420688629150390625), upper := (4705889275362003544626154761021943308981832390117066481392292291/4072410785143773219583494820127477805075645446777343750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint531_valid : endpoint531.Valid 8 := by
  constructor
  · norm_num [endpoint531, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint531, EndpointCache.Valid,
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

theorem endpoint531PositiveFacts : PositiveEndpointFacts 8
    endpoint531 :=
  { valid := endpoint531_valid
    positive := by
      norm_num [endpoint531] }

noncomputable def endpoint532 : EndpointCache :=
  { input := (203/64), certificate := { exponent := 1, mantissa := (203/128) }, enclosure := { lower := (15598806595923941286046524968112011459760330318016/13513382319594401862095663801095038971355319230855), upper := (16543648845482804455514525170808243189881201681324607/14331907191524119917742601151332795617620269995695360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint532_valid : endpoint532.Valid 8 := by
  constructor
  · norm_num [endpoint532, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint532, EndpointCache.Valid,
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

theorem endpoint532PositiveFacts : PositiveEndpointFacts 8
    endpoint532 :=
  { valid := endpoint532_valid
    positive := by
      norm_num [endpoint532] }

noncomputable def endpoint533 : EndpointCache :=
  { input := (837/256), certificate := { exponent := 1, mantissa := (837/512) }, enclosure := { lower := (3250979147751476399994914990671802084436045553429228997312/2744260675850876499033699743585096935113810125182534710735), upper := (103199083589740518579503323723133191755835580305184098548432533/87113810894210223585325764660365317108252788613794381857571840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint533_valid : endpoint533.Valid 8 := by
  constructor
  · norm_num [endpoint533, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint533, EndpointCache.Valid,
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

theorem endpoint533PositiveFacts : PositiveEndpointFacts 8
    endpoint533 :=
  { valid := endpoint533_valid
    positive := by
      norm_num [endpoint533] }

noncomputable def endpoint534 : EndpointCache :=
  { input := (105/32), certificate := { exponent := 1, mantissa := (105/64) }, enclosure := { lower := (10318815637222836451633383922828043624441408/8684231054992924382864039154359216490939333), upper := (6604042105070261773004352654226520271262489697/5557907875195471605032985058789898554201173120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint534_valid : endpoint534.Valid 8 := by
  constructor
  · norm_num [endpoint534, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint534, EndpointCache.Valid,
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

theorem endpoint534PositiveFacts : PositiveEndpointFacts 8
    endpoint534 :=
  { valid := endpoint534_valid
    positive := by
      norm_num [endpoint534] }

noncomputable def endpoint535 : EndpointCache :=
  { input := (103/32), certificate := { exponent := 1, mantissa := (103/64) }, enclosure := { lower := (551954357737906046971671804793102294936266176/472162209593972883213160200580102809881377515), upper := (7276966361114739006086651812979870379569030515099/6224986571286938492282304084448075445476081157760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint535_valid : endpoint535.Valid 8 := by
  constructor
  · norm_num [endpoint535, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint535, EndpointCache.Valid,
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

theorem endpoint535PositiveFacts : PositiveEndpointFacts 8
    endpoint535 :=
  { valid := endpoint535_valid
    positive := by
      norm_num [endpoint535] }

noncomputable def endpoint536 : EndpointCache :=
  { input := (213/64), certificate := { exponent := 1, mantissa := (213/128) }, enclosure := { lower := (2308444324991129466225963518225897308376383147456/1919849376416485427852488844671695967539864528555), upper := (41958284663135601008382321364319866604731936497539441/34895182265746039136646837240752745906004577671015680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint536_valid : endpoint536.Valid 8 := by
  constructor
  · norm_num [endpoint536, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint536, EndpointCache.Valid,
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

theorem endpoint536PositiveFacts : PositiveEndpointFacts 8
    endpoint536 :=
  { valid := endpoint536_valid
    positive := by
      norm_num [endpoint536] }

noncomputable def endpoint537 : EndpointCache :=
  { input := (833/256), certificate := { exponent := 1, mantissa := (833/512) }, enclosure := { lower := (21677415411800043392871422569839946202317657600517969971264/18372930084988049302065985854257788351521625187530517578125), upper := (2641523171553217702701886658495667491779883672406541501356449099/2238851768436303735752552772256437057363019158851718750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint537_valid : endpoint537.Valid 8 := by
  constructor
  · norm_num [endpoint537, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint537, EndpointCache.Valid,
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

theorem endpoint537PositiveFacts : PositiveEndpointFacts 8
    endpoint537 :=
  { valid := endpoint537_valid
    positive := by
      norm_num [endpoint537] }

noncomputable def endpoint538 : EndpointCache :=
  { input := (429/128), certificate := { exponent := 1, mantissa := (429/256) }, enclosure := { lower := (127698038187320929342025099638693352579658862442755264/105585599396407322483967256977481311774944915771484375), upper := (65381396501779361781887424568056201745443478139103736523/54059826890960549111791235572470431628771796875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint538_valid : endpoint538.Valid 8 := by
  constructor
  · norm_num [endpoint538, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint538, EndpointCache.Valid,
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

theorem endpoint538PositiveFacts : PositiveEndpointFacts 8
    endpoint538 :=
  { valid := endpoint538_valid
    positive := by
      norm_num [endpoint538] }

noncomputable def endpoint539 : EndpointCache :=
  { input := (211/64), certificate := { exponent := 1, mantissa := (211/128) }, enclosure := { lower := (229643485612822011920721992611006534877632/192496469885219225626375924369703612327355), upper := (12404422700927029459843720774959056500789579507/10397889317320001691434321930753910323474407680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint539_valid : endpoint539.Valid 8 := by
  constructor
  · norm_num [endpoint539, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint539, EndpointCache.Valid,
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

theorem endpoint539PositiveFacts : PositiveEndpointFacts 8
    endpoint539 :=
  { valid := endpoint539_valid
    positive := by
      norm_num [endpoint539] }

noncomputable def endpoint540 : EndpointCache :=
  { input := (109/32), certificate := { exponent := 1, mantissa := (109/64) }, enclosure := { lower := (12761389841848524355904241749966476781563456/10412259399155574800863799649850017493880805), upper := (178046913640133068486128134496183997415115713357/145271843137018579621651732714707444074624991360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint540_valid : endpoint540.Valid 8 := by
  constructor
  · norm_num [endpoint540, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint540, EndpointCache.Valid,
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

theorem endpoint540PositiveFacts : PositiveEndpointFacts 8
    endpoint540 :=
  { valid := endpoint540_valid
    positive := by
      norm_num [endpoint540] }

noncomputable def endpoint541 : EndpointCache :=
  { input := (215/64), certificate := { exponent := 1, mantissa := (215/128) }, enclosure := { lower := (798183441247611708464562237905421830474475742016/658700379450869521199686143214553147767130402121), upper := (6276002463386231946748820782049088923670097779684703/5179266983567979778118675046075572179014693904677120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint541_valid : endpoint541.Valid 8 := by
  constructor
  · norm_num [endpoint541, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint541, EndpointCache.Valid,
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

theorem endpoint541PositiveFacts : PositiveEndpointFacts 8
    endpoint541 :=
  { valid := endpoint541_valid
    positive := by
      norm_num [endpoint541] }

noncomputable def endpoint542 : EndpointCache :=
  { input := (111/32), certificate := { exponent := 1, mantissa := (111/64) }, enclosure := { lower := (169264315366172959409090852778150461435715136/136087064966961144037214107811450958251953125), upper := (114519401296687483899743209497979766570043172433/92072619954789711165749430656433105468750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint542_valid : endpoint542.Valid 8 := by
  constructor
  · norm_num [endpoint542, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint542, EndpointCache.Valid,
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

theorem endpoint542PositiveFacts : PositiveEndpointFacts 8
    endpoint542 :=
  { valid := endpoint542_valid
    positive := by
      norm_num [endpoint542] }

noncomputable def endpoint543 : EndpointCache :=
  { input := (225/64), certificate := { exponent := 1, mantissa := (225/128) }, enclosure := { lower := (1274403772690099780698143846218725516207255499456/1013670233976586809285665547685875621141991978671), upper := (8156184262322951995596829459173569067245890969410679/6487489497450155579428259505189603975308748663494400) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint543_valid : endpoint543.Valid 8 := by
  constructor
  · norm_num [endpoint543, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint543, EndpointCache.Valid,
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

theorem endpoint543PositiveFacts : PositiveEndpointFacts 8
    endpoint543 :=
  { valid := endpoint543_valid
    positive := by
      norm_num [endpoint543] }

noncomputable def endpoint544 : EndpointCache :=
  { input := (229/64), certificate := { exponent := 1, mantissa := (229/128) }, enclosure := { lower := (9694896167569006632382928712928071371200/7604800906331319011372113473214766808027), upper := (81193371593857400766390082445160625632080965/63689121190395320817525540036248927050539264) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint544_valid : endpoint544.Valid 8 := by
  constructor
  · norm_num [endpoint544, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint544, EndpointCache.Valid,
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

theorem endpoint544PositiveFacts : PositiveEndpointFacts 8
    endpoint544 :=
  { valid := endpoint544_valid
    positive := by
      norm_num [endpoint544] }

noncomputable def endpoint545 : EndpointCache :=
  { input := (759/256), certificate := { exponent := 1, mantissa := (759/512) }, enclosure := { lower := (8544502250713626688996385899079686207083742609039452535232/7861898192638441336191771823905752809941234068153938811355), upper := (201240120235206233387396996988888547310186337881612153148351979/185163426233020570349988609996628290179735944773161566885032960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint545_valid : endpoint545.Valid 8 := by
  constructor
  · norm_num [endpoint545, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint545, EndpointCache.Valid,
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

theorem endpoint545PositiveFacts : PositiveEndpointFacts 8
    endpoint545 :=
  { valid := endpoint545_valid
    positive := by
      norm_num [endpoint545] }

noncomputable def endpoint546 : EndpointCache :=
  { input := (777/256), certificate := { exponent := 1, mantissa := (777/512) }, enclosure := { lower := (10778634550516271163143094604750791540514622719390935877184/9708182182056125112061256403616862246625242479661231940645), upper := (408380912260133442255872747831387454804750604191407531339323937/367823606513742468245776882620235676800137187069404755767157760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint546_valid : endpoint546.Valid 8 := by
  constructor
  · norm_num [endpoint546, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint546, EndpointCache.Valid,
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

theorem endpoint546PositiveFacts : PositiveEndpointFacts 8
    endpoint546 :=
  { valid := endpoint546_valid
    positive := by
      norm_num [endpoint546] }

noncomputable def endpoint547 : EndpointCache :=
  { input := (393/128), certificate := { exponent := 1, mantissa := (393/256) }, enclosure := { lower := (6707479589315153932652861912631033238128349482404800/5979321697824620899724691528217554552234157034843139), upper := (449884078004680960392593473757117924194902185350220205265/401045064916492972986334510180607818927449380640999019008) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint547_valid : endpoint547.Valid 8 := by
  constructor
  · norm_num [endpoint547, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint547, EndpointCache.Valid,
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

theorem endpoint547PositiveFacts : PositiveEndpointFacts 8
    endpoint547 :=
  { valid := endpoint547_valid
    positive := by
      norm_num [endpoint547] }

noncomputable def endpoint548 : EndpointCache :=
  { input := (793/256), certificate := { exponent := 1, mantissa := (793/512) }, enclosure := { lower := (920469868095299872295025855124823465728459005417152/814109854312911052562558221775574317734222412109375), upper := (57496230727195804595779160526629950354281913397754353483/50852557939801675987267636764989474182950468750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint548_valid : endpoint548.Valid 8 := by
  constructor
  · norm_num [endpoint548, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint548, EndpointCache.Valid,
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

theorem endpoint548PositiveFacts : PositiveEndpointFacts 8
    endpoint548 :=
  { valid := endpoint548_valid
    positive := by
      norm_num [endpoint548] }

noncomputable def endpoint549 : EndpointCache :=
  { input := (3111/1024), certificate := { exponent := 1, mantissa := (3111/2048) }, enclosure := { lower := (151753740699116572713073910663877812378120175186036426616912725184/136564038158579400092204995566778498936710978370552587031316394135), upper := (92083130703291928603441587016346465001026504807340303823085012544721739/82866121915507178288635073332808735245089227085685340307148858934415360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint549_valid : endpoint549.Valid 8 := by
  constructor
  · norm_num [endpoint549, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint549, EndpointCache.Valid,
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

theorem endpoint549PositiveFacts : PositiveEndpointFacts 8
    endpoint549 :=
  { valid := endpoint549_valid
    positive := by
      norm_num [endpoint549] }

noncomputable def endpoint550 : EndpointCache :=
  { input := (1589/512), certificate := { exponent := 1, mantissa := (1589/1024) }, enclosure := { lower := (2364421881033885010320294667038852269914528676392740032/2087724222783818040601413488419712566767224337354829335), upper := (1099210291725436146577673367255027193606316872857786148407017/970574640275305871803434725112370693439815525538910738524160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint550_valid : endpoint550.Valid 8 := by
  constructor
  · norm_num [endpoint550, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint550, EndpointCache.Valid,
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

theorem endpoint550PositiveFacts : PositiveEndpointFacts 8
    endpoint550 :=
  { valid := endpoint550_valid
    positive := by
      norm_num [endpoint550] }

noncomputable def endpoint551 : EndpointCache :=
  { input := (785/256), certificate := { exponent := 1, mantissa := (785/512) }, enclosure := { lower := (2387196044574033489084425403797080243953884751523927930688/2130462009546504422104588961225308194165089194543717574553), upper := (1918923698319237686384672568808303806459092752800617878205785273/1712550581753862114664552790591351738797665298142021935128683520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint551_valid : endpoint551.Valid 8 := by
  constructor
  · norm_num [endpoint551, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint551, EndpointCache.Valid,
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

theorem endpoint551PositiveFacts : PositiveEndpointFacts 8
    endpoint551 :=
  { valid := endpoint551_valid
    positive := by
      norm_num [endpoint551] }

noncomputable def endpoint552 : EndpointCache :=
  { input := (401/128), certificate := { exponent := 1, mantissa := (401/256) }, enclosure := { lower := (345624413968849568873016217918722388696220224/302666592660630864078267622599486548511781845), upper := (70960840764365746570865662550938642274887311419893/62141083472339443965637282131145782248050954160640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint552_valid : endpoint552.Valid 8 := by
  constructor
  · norm_num [endpoint552, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint552, EndpointCache.Valid,
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

theorem endpoint552PositiveFacts : PositiveEndpointFacts 8
    endpoint552 :=
  { valid := endpoint552_valid
    positive := by
      norm_num [endpoint552] }

noncomputable def endpoint553 : EndpointCache :=
  { input := (199/64), certificate := { exponent := 1, mantissa := (199/128) }, enclosure := { lower := (6594507990065570898180941241109259998400/5813100856138962435382991229033494159127), upper := (335950620208865299532412016321506873733840295/296142610015143302308151105171882326442565888) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint553_valid : endpoint553.Valid 8 := by
  constructor
  · norm_num [endpoint553, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint553, EndpointCache.Valid,
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

theorem endpoint553PositiveFacts : PositiveEndpointFacts 8
    endpoint553 :=
  { valid := endpoint553_valid
    positive := by
      norm_num [endpoint553] }

noncomputable def endpoint554 : EndpointCache :=
  { input := (209/64), certificate := { exponent := 1, mantissa := (209/128) }, enclosure := { lower := (4187675378398105204002248061671339877231301793600/3538528241031604909868969922783919627778111044953), upper := (20368853341490921083462007532957999317344919909797835/17211401364377726281602669704420985069512732122651392) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint554_valid : endpoint554.Valid 8 := by
  constructor
  · norm_num [endpoint554, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint554, EndpointCache.Valid,
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

theorem endpoint554PositiveFacts : PositiveEndpointFacts 8
    endpoint554 :=
  { valid := endpoint554_valid
    positive := by
      norm_num [endpoint554] }

noncomputable def endpoint555 : EndpointCache :=
  { input := (3349/1024), certificate := { exponent := 1, mantissa := (3349/2048) }, enclosure := { lower := (48802475654095705117881006499210524944000146213553785352000/41185426067364879849116050540835095188244696462210673499897), upper := (95635452125119884263553594997563624765307144852063211133437493575/80708749545826001255681259965443940226446768099880108939647299584) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint555_valid : endpoint555.Valid 8 := by
  constructor
  · norm_num [endpoint555, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint555, EndpointCache.Valid,
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

theorem endpoint555PositiveFacts : PositiveEndpointFacts 8
    endpoint555 :=
  { valid := endpoint555_valid
    positive := by
      norm_num [endpoint555] }

noncomputable def endpoint556 : EndpointCache :=
  { input := (827/256), certificate := { exponent := 1, mantissa := (827/512) }, enclosure := { lower := (1549777824333930339010985400944090648870568791670477535168/1321628697401734200681375583141295199822485040733016940915), upper := (1312426270530662375425594638029852361238479433475374914431425979/1119218619137263804378621549832039557379271811774673930379985920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint556_valid : endpoint556.Valid 8 := by
  constructor
  · norm_num [endpoint556, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint556, EndpointCache.Valid,
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

theorem endpoint556PositiveFacts : PositiveEndpointFacts 8
    endpoint556 :=
  { valid := endpoint556_valid
    positive := by
      norm_num [endpoint556] }

noncomputable def endpoint557 : EndpointCache :=
  { input := (845/256), certificate := { exponent := 1, mantissa := (845/512) }, enclosure := { lower := (5013420010802783519781996208461743466543896656988404271168/4198284522664160777230873797149502017028647586249212224653), upper := (333693240812892573489061493092778996778934001646525232158746281/279437817828526541332486959938270854253426783340747565672903680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint557_valid : endpoint557.Valid 8 := by
  constructor
  · norm_num [endpoint557, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint557, EndpointCache.Valid,
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

theorem endpoint557PositiveFacts : PositiveEndpointFacts 8
    endpoint557 :=
  { valid := endpoint557_valid
    positive := by
      norm_num [endpoint557] }

noncomputable def endpoint558 : EndpointCache :=
  { input := (855/256), certificate := { exponent := 1, mantissa := (855/512) }, enclosure := { lower := (5652255933407302119297594055859085448483950165292893062848/4687074661050542749283973240370083381246647808262294837503), upper := (549851465206271682804486080684077904815317591183507471297365687/455958623026996798650344916823201711327673898787756041792291840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint558_valid : endpoint558.Valid 8 := by
  constructor
  · norm_num [endpoint558, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint558, EndpointCache.Valid,
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

theorem endpoint558PositiveFacts : PositiveEndpointFacts 8
    endpoint558 :=
  { valid := endpoint558_valid
    positive := by
      norm_num [endpoint558] }

noncomputable def endpoint559 : EndpointCache :=
  { input := (221/64), certificate := { exponent := 1, mantissa := (221/128) }, enclosure := { lower := (37059100037372394428982462029362501935014300546368/29903743695352281452813460410626958135577593900145), upper := (12406246590642031545673458276274574398848006855892817/10010853274013317606357244592849886292771822204110080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint559_valid : endpoint559.Valid 8 := by
  constructor
  · norm_num [endpoint559, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint559, EndpointCache.Valid,
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

theorem endpoint559PositiveFacts : PositiveEndpointFacts 8
    endpoint559 :=
  { valid := endpoint559_valid
    positive := by
      norm_num [endpoint559] }

noncomputable def endpoint560 : EndpointCache :=
  { input := (447/128), certificate := { exponent := 1, mantissa := (447/256) }, enclosure := { lower := (123986637517551380030650463524148213819004201709592384/99147404003272114591889661488274913983496851379043385), upper := (9458692738633757497050709863121121124313043964541562176787/7563757156601623077986078495617516637973007798004461754880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint560_valid : endpoint560.Valid 8 := by
  constructor
  · norm_num [endpoint560, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint560, EndpointCache.Valid,
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

theorem endpoint560PositiveFacts : PositiveEndpointFacts 8
    endpoint560 :=
  { valid := endpoint560_valid
    positive := by
      norm_num [endpoint560] }

noncomputable def endpoint561 : EndpointCache :=
  { input := (223/64), certificate := { exponent := 1, mantissa := (223/128) }, enclosure := { lower := (218023730230458109701940295536954225318976/174658099917470255867035966088058152877405), upper := (12446538889947653179641380189717378442828828893/9970881608088541966937349232035063831465296640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint561_valid : endpoint561.Valid 8 := by
  constructor
  · norm_num [endpoint561, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint561, EndpointCache.Valid,
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

theorem endpoint561PositiveFacts : PositiveEndpointFacts 8
    endpoint561 :=
  { valid := endpoint561_valid
    positive := by
      norm_num [endpoint561] }

noncomputable def endpoint562 : EndpointCache :=
  { input := (115/32), certificate := { exponent := 1, mantissa := (115/64) }, enclosure := { lower := (342063540565520296396613359803932843502399424/267405057971925464918511430520464993820996979), upper := (5035175390307915357289685801202187981102658068811/3936202453346742843600488257261244709045075530880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint562_valid : endpoint562.Valid 8 := by
  constructor
  · norm_num [endpoint562, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint562, EndpointCache.Valid,
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

theorem endpoint562PositiveFacts : PositiveEndpointFacts 8
    endpoint562 :=
  { valid := endpoint562_valid
    positive := by
      norm_num [endpoint562] }

noncomputable def endpoint563 : EndpointCache :=
  { input := (931/256), certificate := { exponent := 1, mantissa := (931/512) }, enclosure := { lower := (2705184882928635406511452387268534140321924216000/2095285377368051572236799989073231109992718026071), upper := (368424545009799213898115807458359443744097259150255225/285361106114509679726074264111861491332128253406661632) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint563_valid : endpoint563.Valid 8 := by
  constructor
  · norm_num [endpoint563, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint563, EndpointCache.Valid,
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

theorem endpoint563PositiveFacts : PositiveEndpointFacts 8
    endpoint563 :=
  { valid := endpoint563_valid
    positive := by
      norm_num [endpoint563] }

noncomputable def endpoint564 : EndpointCache :=
  { input := (227/64), certificate := { exponent := 1, mantissa := (227/128) }, enclosure := { lower := (48890684675406295270036417681107212659986817759936/38616192713548869097157673720232688029632568359375), upper := (2841135508771494915820333150306570045284160101514390727/2244064190969751880974026735230161966778007812500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint564_valid : endpoint564.Valid 8 := by
  constructor
  · norm_num [endpoint564, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint564, EndpointCache.Valid,
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

theorem endpoint564PositiveFacts : PositiveEndpointFacts 8
    endpoint564 :=
  { valid := endpoint564_valid
    positive := by
      norm_num [endpoint564] }

noncomputable def endpoint565 : EndpointCache :=
  { input := (117/32), certificate := { exponent := 1, mantissa := (117/64) }, enclosure := { lower := (409547744571073405141430682781591761834651200/315902291368238235704777285038509742315016421), upper := (52422112085264203609752682736089230415909641865/40435493295134494170211492484929247016322101888) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint565_valid : endpoint565.Valid 8 := by
  constructor
  · norm_num [endpoint565, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint565, EndpointCache.Valid,
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

theorem endpoint565PositiveFacts : PositiveEndpointFacts 8
    endpoint565 :=
  { valid := endpoint565_valid
    positive := by
      norm_num [endpoint565] }

noncomputable def endpoint566 : EndpointCache :=
  { input := (237/64), certificate := { exponent := 1, mantissa := (237/128) }, enclosure := { lower := (76689429998883197177573788549402828277772741513536/58578348598168502630397265390858273452301025390625), upper := (1550967056046104093683626722199476552745165362201206979/1184688522049359797197154295264717722299335937500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint566_valid : endpoint566.Valid 8 := by
  constructor
  · norm_num [endpoint566, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint566, EndpointCache.Valid,
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

theorem endpoint566PositiveFacts : PositiveEndpointFacts 8
    endpoint566 :=
  { valid := endpoint566_valid
    positive := by
      norm_num [endpoint566] }

noncomputable def endpoint567 : EndpointCache :=
  { input := (119/32), certificate := { exponent := 1, mantissa := (119/64) }, enclosure := { lower := (170484378455055244218739834225701098816/129805078002935329925860726760531673105), upper := (370974013266575318930030046653076913300151/282455849734387277918672941430916920676480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint567_valid : endpoint567.Valid 8 := by
  constructor
  · norm_num [endpoint567, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint567, EndpointCache.Valid,
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

theorem endpoint567PositiveFacts : PositiveEndpointFacts 8
    endpoint567 :=
  { valid := endpoint567_valid
    positive := by
      norm_num [endpoint567] }

noncomputable def endpoint568 : EndpointCache :=
  { input := (233/64), certificate := { exponent := 1, mantissa := (233/128) }, enclosure := { lower := (4935413788575755191254388524888692486291116263232/3819520397167155105270634475113849046872935426585), upper := (294387566010232084928868890663971983142429866578825321/227826752650226467719182805171590867947876852324942080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint568_valid : endpoint568.Valid 8 := by
  constructor
  · norm_num [endpoint568, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint568, EndpointCache.Valid,
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

theorem endpoint568PositiveFacts : PositiveEndpointFacts 8
    endpoint568 :=
  { valid := endpoint568_valid
    positive := by
      norm_num [endpoint568] }

noncomputable def endpoint569 : EndpointCache :=
  { input := (241/64), certificate := { exponent := 1, mantissa := (241/128) }, enclosure := { lower := (6374353373248733271252102938469458907026624/4807517003170213501810689911573118348675735), upper := (393272112082784033968765059391559100345296419319/296604569027589492207712324784415109639898146560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint569_valid : endpoint569.Valid 8 := by
  constructor
  · norm_num [endpoint569, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint569, EndpointCache.Valid,
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

theorem endpoint569PositiveFacts : PositiveEndpointFacts 8
    endpoint569 :=
  { valid := endpoint569_valid
    positive := by
      norm_num [endpoint569] }

noncomputable def endpoint570 : EndpointCache :=
  { input := (471/128), certificate := { exponent := 1, mantissa := (471/256) }, enclosure := { lower := (335853057945039479267103193810748368399885525358469184/257787752518462110251625289899536859430432732611633645), upper := (26997212616873220612976532936335590932585874268028467702591/20722010698444058270466647303284370908455904778253558919680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint570_valid : endpoint570.Valid 8 := by
  constructor
  · norm_num [endpoint570, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint570, EndpointCache.Valid,
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

theorem endpoint570PositiveFacts : PositiveEndpointFacts 8
    endpoint570 :=
  { valid := endpoint570_valid
    positive := by
      norm_num [endpoint570] }

noncomputable def endpoint571 : EndpointCache :=
  { input := (969/256), certificate := { exponent := 1, mantissa := (969/512) }, enclosure := { lower := (103723349131199668635961514768322289285747058075776509204032/77923784234703602579813984203229259387611085496392303829605), upper := (34306705739686558961495189303365307985569846268305585609083747879/25773447483196685960478634903186484000971141750102747276249512960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint571_valid : endpoint571.Valid 8 := by
  constructor
  · norm_num [endpoint571, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint571, EndpointCache.Valid,
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

theorem endpoint571PositiveFacts : PositiveEndpointFacts 8
    endpoint571 :=
  { valid := endpoint571_valid
    positive := by
      norm_num [endpoint571] }

noncomputable def endpoint572 : EndpointCache :=
  { input := (239/64), certificate := { exponent := 1, mantissa := (239/128) }, enclosure := { lower := (2393559482983034589473223674860561257798205256000/1816632488306864068413816077144166556227556528929), upper := (146447545706255575470977625649395166161799688064061825/111148842164567171161830922863988686576226818665991936) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint572_valid : endpoint572.Valid 8 := by
  constructor
  · norm_num [endpoint572, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint572, EndpointCache.Valid,
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

theorem endpoint572PositiveFacts : PositiveEndpointFacts 8
    endpoint572 :=
  { valid := endpoint572_valid
    positive := by
      norm_num [endpoint572] }

noncomputable def endpoint573 : EndpointCache :=
  { input := (247/64), certificate := { exponent := 1, mantissa := (247/128) }, enclosure := { lower := (8269716660014169463324983097481324761238848/6123424287949319477775134146213531494140625), upper := (40223902575509045307319817035991852850026359717/29784335736585489939898252487182617187500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint573_valid : endpoint573.Valid 8 := by
  constructor
  · norm_num [endpoint573, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint573, EndpointCache.Valid,
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

theorem endpoint573PositiveFacts : PositiveEndpointFacts 8
    endpoint573 :=
  { valid := endpoint573_valid
    positive := by
      norm_num [endpoint573] }

noncomputable def endpoint574 : EndpointCache :=
  { input := (121/32), certificate := { exponent := 1, mantissa := (121/64) }, enclosure := { lower := (2916013743075856824254549232102095100069196352/2192401463848579101979896264943611602783203125), upper := (4105747417895610640341909172365916407963583912751/3086901261098799375587693941040605136718750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint574_valid : endpoint574.Valid 8 := by
  constructor
  · norm_num [endpoint574, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint574, EndpointCache.Valid,
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

theorem endpoint574PositiveFacts : PositiveEndpointFacts 8
    endpoint574 :=
  { valid := endpoint574_valid
    positive := by
      norm_num [endpoint574] }

noncomputable def endpoint575 : EndpointCache :=
  { input := (997/256), certificate := { exponent := 1, mantissa := (997/512) }, enclosure := { lower := (752182483604184005351856571402971063295569367724224/553248927707532569729275822045031789458364062057095), upper := (767924173712388875138960518687764105408724385083191513967/564827321266595811348570106448790214748148705147825884160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint575_valid : endpoint575.Valid 8 := by
  constructor
  · norm_num [endpoint575, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint575, EndpointCache.Valid,
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

theorem endpoint575PositiveFacts : PositiveEndpointFacts 8
    endpoint575 :=
  { valid := endpoint575_valid
    positive := by
      norm_num [endpoint575] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
