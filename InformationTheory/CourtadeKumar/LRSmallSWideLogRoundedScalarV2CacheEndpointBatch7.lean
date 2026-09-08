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

noncomputable def endpoint448 : EndpointCache :=
  { input := (171/64), certificate := { exponent := 1, mantissa := (171/128) }, enclosure := { lower := (222292673107595825962525212858499808227213286336/226187515331400639033066273636139698408417894915), upper := (1081231581163647478245180123951152337007142405329619/1100176074571932708256834354966183493058544640866560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint448_valid : endpoint448.Valid 8 := by
  constructor
  · norm_num [endpoint448, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint448, EndpointCache.Valid,
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

theorem endpoint448PositiveFacts : PositiveEndpointFacts 8
    endpoint448 :=
  { valid := endpoint448_valid
    positive := by
      norm_num [endpoint448] }

noncomputable def endpoint449 : EndpointCache :=
  { input := (671/256), certificate := { exponent := 1, mantissa := (671/512) }, enclosure := { lower := (5675406545827531834349878893021841475896121963749966400/5889845871448014278898745594649359242048909393698469717), upper := (4604007803747091459192732370064921819471889652310006271835/4777965357326347583339366815898410073965494498285470290944) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint449_valid : endpoint449.Valid 8 := by
  constructor
  · norm_num [endpoint449, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint449, EndpointCache.Valid,
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

theorem endpoint449PositiveFacts : PositiveEndpointFacts 8
    endpoint449 :=
  { valid := endpoint449_valid
    positive := by
      norm_num [endpoint449] }

noncomputable def endpoint450 : EndpointCache :=
  { input := (2729/1024), certificate := { exponent := 1, mantissa := (2729/2048) }, enclosure := { lower := (59106205143202698341732367449446160706328589928119969671121368000/60298996839334765434602011834415513388427996553053050977438505123), upper := (660688227134867641132231666582984927085170015774371729685062900813234515/674021221886134578671734334652907258007633930622082154976991971248812032) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint450_valid : endpoint450.Valid 8 := by
  constructor
  · norm_num [endpoint450, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint450, EndpointCache.Valid,
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

theorem endpoint450PositiveFacts : PositiveEndpointFacts 8
    endpoint450 :=
  { valid := endpoint450_valid
    positive := by
      norm_num [endpoint450] }

noncomputable def endpoint451 : EndpointCache :=
  { input := (173/64), certificate := { exponent := 1, mantissa := (173/128) }, enclosure := { lower := (461645262985383728181978313604103584026734724288/464241062183491107975600030425919512164994973015), upper := (2920763680759696120980147125416292672386364711336537/2937186880283207741431910592500446193537613909269760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint451_valid : endpoint451.Valid 8 := by
  constructor
  · norm_num [endpoint451, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint451, EndpointCache.Valid,
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

theorem endpoint451PositiveFacts : PositiveEndpointFacts 8
    endpoint451 :=
  { valid := endpoint451_valid
    positive := by
      norm_num [endpoint451] }

noncomputable def endpoint452 : EndpointCache :=
  { input := (10791/4096), certificate := { exponent := 1, mantissa := (10791/8192) }, enclosure := { lower := (48094290020245489180160131093121903216532253650118751008622245833763864000/49648201031327935190031994376441197677761133025849389806951159689738319019), upper := (85889477943191925486069576052315043273387001971328832890319505709886120942016905/88664537701003181026729777349133771520015785981011287883082570238877315449995264) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint452_valid : endpoint452.Valid 8 := by
  constructor
  · norm_num [endpoint452, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint452, EndpointCache.Valid,
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

theorem endpoint452PositiveFacts : PositiveEndpointFacts 8
    endpoint452 :=
  { valid := endpoint452_valid
    positive := by
      norm_num [endpoint452] }

noncomputable def endpoint453 : EndpointCache :=
  { input := (10971/4096), certificate := { exponent := 1, mantissa := (10971/8192) }, enclosure := { lower := (66600577992346762246096127766161965204421751332305914810891295679971400000/67598017903353654807887195298598051487244392995165204801171121804039739777), upper := (1330153160840898486682879326240182991376236321297012750996753861980150573849260625/1350074102975497915773984621674348949716187792361167006148650557097974870641262592) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint453_valid : endpoint453.Valid 8 := by
  constructor
  · norm_num [endpoint453, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint453, EndpointCache.Valid,
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

theorem endpoint453PositiveFacts : PositiveEndpointFacts 8
    endpoint453 :=
  { valid := endpoint453_valid
    positive := by
      norm_num [endpoint453] }

noncomputable def endpoint454 : EndpointCache :=
  { input := (341/128), certificate := { exponent := 1, mantissa := (341/256) }, enclosure := { lower := (6416539631379479455070669853078646921626920384/6548476954474781216572463665698281011125976395), upper := (101843318840150444637561751305055595145052485080953/103937426221423727469438143301963116208591497341440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint454_valid : endpoint454.Valid 8 := by
  constructor
  · norm_num [endpoint454, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint454, EndpointCache.Valid,
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

theorem endpoint454PositiveFacts : PositiveEndpointFacts 8
    endpoint454 :=
  { valid := endpoint454_valid
    positive := by
      norm_num [endpoint454] }

noncomputable def endpoint455 : EndpointCache :=
  { input := (347/128), certificate := { exponent := 1, mantissa := (347/256) }, enclosure := { lower := (7587670256184414800445603634240168575509165632/7608254273880376728724747367942278326305653605), upper := (1348055871945576891553174098918715690763760530781853/1351712887314683251132153516378096936564767642078720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint455_valid : endpoint455.Valid 8 := by
  constructor
  · norm_num [endpoint455, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint455, EndpointCache.Valid,
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

theorem endpoint455PositiveFacts : PositiveEndpointFacts 8
    endpoint455 :=
  { valid := endpoint455_valid
    positive := by
      norm_num [endpoint455] }

noncomputable def endpoint456 : EndpointCache :=
  { input := (685/256), certificate := { exponent := 1, mantissa := (685/512) }, enclosure := { lower := (43816242989553622267899430984417355909381653184/44517781218484127842226635660150488084844479279), upper := (4390638003807265667344450261666838212888927107846977/4460936065413358090521635902493708337461901649351680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint456_valid : endpoint456.Valid 8 := by
  constructor
  · norm_num [endpoint456, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint456, EndpointCache.Valid,
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

theorem endpoint456PositiveFacts : PositiveEndpointFacts 8
    endpoint456 :=
  { valid := endpoint456_valid
    positive := by
      norm_num [endpoint456] }

noncomputable def endpoint457 : EndpointCache :=
  { input := (697/256), certificate := { exponent := 1, mantissa := (697/512) }, enclosure := { lower := (316470852751598953948257950226536325328860112448/315962795549977633545153441989325232195280198565), upper := (225874112721770544673611586186866967636024895912722709/225511494142294436434915275844157119324272945561400320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint457_valid : endpoint457.Valid 8 := by
  constructor
  · norm_num [endpoint457, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint457, EndpointCache.Valid,
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

theorem endpoint457PositiveFacts : PositiveEndpointFacts 8
    endpoint457 :=
  { valid := endpoint457_valid
    positive := by
      norm_num [endpoint457] }

noncomputable def endpoint458 : EndpointCache :=
  { input := (689/256), certificate := { exponent := 1, mantissa := (689/512) }, enclosure := { lower := (3327763555039049383877727046861888391299735861055180909632/3361160633541184642963057063038061775013803051006819728605), upper := (180604386837319034147150694758017371567167065344168298607629169/182416909903547172942891032925201688653549119184242120310850560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint458_valid : endpoint458.Valid 8 := by
  constructor
  · norm_num [endpoint458, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint458, EndpointCache.Valid,
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

theorem endpoint458PositiveFacts : PositiveEndpointFacts 8
    endpoint458 :=
  { valid := endpoint458_valid
    positive := by
      norm_num [endpoint458] }

noncomputable def endpoint459 : EndpointCache :=
  { input := (1401/512), certificate := { exponent := 1, mantissa := (1401/1024) }, enclosure := { lower := (18272016872448318396572184662187872690480611113949764453708736/18151907149802955359954227385588065516571514308452606201171875), upper := (17475649591555729857657863483220181989755622744274107405211550438161/17360774428585943353545982339214595269097261428833007812500000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint459_valid : endpoint459.Valid 8 := by
  constructor
  · norm_num [endpoint459, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint459, EndpointCache.Valid,
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

theorem endpoint459PositiveFacts : PositiveEndpointFacts 8
    endpoint459 :=
  { valid := endpoint459_valid
    positive := by
      norm_num [endpoint459] }

noncomputable def endpoint460 : EndpointCache :=
  { input := (177/64), certificate := { exponent := 1, mantissa := (177/128) }, enclosure := { lower := (4029735614614975828231285596814209325475992271936/3961336608976297910335105186783803500518798828125), upper := (60865127765597710133798266205002716132627510979746559/59832028141978003637701428741182568071835937500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint460_valid : endpoint460.Valid 8 := by
  constructor
  · norm_num [endpoint460, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint460, EndpointCache.Valid,
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

theorem endpoint460PositiveFacts : PositiveEndpointFacts 8
    endpoint460 :=
  { valid := endpoint460_valid
    positive := by
      norm_num [endpoint460] }

noncomputable def endpoint461 : EndpointCache :=
  { input := (87/32), certificate := { exponent := 1, mantissa := (87/64) }, enclosure := { lower := (1895441838843706967313070225304198911067200/1895115471829971519955238311895352712488861), upper := (7035880228352562480523918685344648322662491055/7034668631432854282073844613755549268758652032) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint461_valid : endpoint461.Valid 8 := by
  constructor
  · norm_num [endpoint461, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint461, EndpointCache.Valid,
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

theorem endpoint461PositiveFacts : PositiveEndpointFacts 8
    endpoint461 :=
  { valid := endpoint461_valid
    positive := by
      norm_num [endpoint461] }

noncomputable def endpoint462 : EndpointCache :=
  { input := (175/64), certificate := { exponent := 1, mantissa := (175/128) }, enclosure := { lower := (50321179878028525595405672993461638933056/50025882618185252492454386213793403399221), upper := (322055556797617632537126755709330394644225923/320165648756385615951708071768277781755014400) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint462_valid : endpoint462.Valid 8 := by
  constructor
  · norm_num [endpoint462, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint462, EndpointCache.Valid,
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

theorem endpoint462PositiveFacts : PositiveEndpointFacts 8
    endpoint462 :=
  { valid := endpoint462_valid
    positive := by
      norm_num [endpoint462] }

noncomputable def endpoint463 : EndpointCache :=
  { input := (89/32), certificate := { exponent := 1, mantissa := (89/64) }, enclosure := { lower := (9051700489824071781962105477939674816/8849053051976774068451022468339729855), upper := (103116973736462462001624750351275872665967/100808412368119410187794047959326202508160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint463_valid : endpoint463.Valid 8 := by
  constructor
  · norm_num [endpoint463, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint463, EndpointCache.Valid,
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

theorem endpoint463PositiveFacts : PositiveEndpointFacts 8
    endpoint463 :=
  { valid := endpoint463_valid
    positive := by
      norm_num [endpoint463] }

noncomputable def endpoint464 : EndpointCache :=
  { input := (181/64), certificate := { exponent := 1, mantissa := (181/128) }, enclosure := { lower := (2982557075630483965551532476979994017472/2868908294795443810500576164984095207455), upper := (138199766972535604535369667231069912809430887/132933734747641684403354697180703035532634880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint464_valid : endpoint464.Valid 8 := by
  constructor
  · norm_num [endpoint464, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint464, EndpointCache.Valid,
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

theorem endpoint464PositiveFacts : PositiveEndpointFacts 8
    endpoint464 :=
  { valid := endpoint464_valid
    positive := by
      norm_num [endpoint464] }

noncomputable def endpoint465 : EndpointCache :=
  { input := (693/256), certificate := { exponent := 1, mantissa := (693/512) }, enclosure := { lower := (3518397491451869550640986699955705538257174490594153516864/3533050629216547055967672033495822040592054950103759765625), upper := (3602839094280228576277081052349922607888907543974276619399821/3617843844317744185310896162299721769566264268906250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint465_valid : endpoint465.Valid 8 := by
  constructor
  · norm_num [endpoint465, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint465, EndpointCache.Valid,
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

theorem endpoint465PositiveFacts : PositiveEndpointFacts 8
    endpoint465 :=
  { valid := endpoint465_valid
    positive := by
      norm_num [endpoint465] }

noncomputable def endpoint466 : EndpointCache :=
  { input := (705/256), certificate := { exponent := 1, mantissa := (705/512) }, enclosure := { lower := (830521728840742575791332824333035863955693725235617315648/819847027592923677356040896898813160686872423610380379753), upper := (199856752265581353689239522070218158223254942967335056670997411/197287988719961153718957681429730398987688980017601934583761920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint466_valid : endpoint466.Valid 8 := by
  constructor
  · norm_num [endpoint466, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint466, EndpointCache.Valid,
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

theorem endpoint466PositiveFacts : PositiveEndpointFacts 8
    endpoint466 :=
  { valid := endpoint466_valid
    positive := by
      norm_num [endpoint466] }

noncomputable def endpoint467 : EndpointCache :=
  { input := (179/64), certificate := { exponent := 1, mantissa := (179/128) }, enclosure := { lower := (898783788431133175794104257036334443308614436800/873875945750618896469867103620091581905193180403), upper := (41185869018765213149522873606058099700563642016282795/40044491338076360311835190156287076649223572298787072) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint467_valid : endpoint467.Valid 8 := by
  constructor
  · norm_num [endpoint467, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint467, EndpointCache.Valid,
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

theorem endpoint467PositiveFacts : PositiveEndpointFacts 8
    endpoint467 :=
  { valid := endpoint467_valid
    positive := by
      norm_num [endpoint467] }

noncomputable def endpoint468 : EndpointCache :=
  { input := (709/256), certificate := { exponent := 1, mantissa := (709/512) }, enclosure := { lower := (27791025458655459116886906094958898392526824426816/27281460135334768588903700889190955025555806510865), upper := (20176729484484664029027566978559702715020256526437804841/19806776561615207351841509304766860403833924419792163840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint468_valid : endpoint468.Valid 8 := by
  constructor
  · norm_num [endpoint468, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint468, EndpointCache.Valid,
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

theorem endpoint468PositiveFacts : PositiveEndpointFacts 8
    endpoint468 :=
  { valid := endpoint468_valid
    positive := by
      norm_num [endpoint468] }

noncomputable def endpoint469 : EndpointCache :=
  { input := (91/32), certificate := { exponent := 1, mantissa := (91/64) }, enclosure := { lower := (161245382079794198245264631257740420614313152/154283552359160966954007792192332611083984375), upper := (20639409250291909528238061125599108908592165741/19748294701972603770112997400618574218750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint469_valid : endpoint469.Valid 8 := by
  constructor
  · norm_num [endpoint469, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint469, EndpointCache.Valid,
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

theorem endpoint469PositiveFacts : PositiveEndpointFacts 8
    endpoint469 :=
  { valid := endpoint469_valid
    positive := by
      norm_num [endpoint469] }

noncomputable def endpoint470 : EndpointCache :=
  { input := (185/64), certificate := { exponent := 1, mantissa := (185/128) }, enclosure := { lower := (112734119384715561090172033651638949735542818752/106205383389909010701724794448837142703173415027), upper := (5339087981698268942669249937980566112637072814510787/5029886957346090746833686265096927078422292935678720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint470_valid : endpoint470.Valid 8 := by
  constructor
  · norm_num [endpoint470, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint470, EndpointCache.Valid,
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

theorem endpoint470PositiveFacts : PositiveEndpointFacts 8
    endpoint470 :=
  { valid := endpoint470_valid
    positive := by
      norm_num [endpoint470] }

noncomputable def endpoint471 : EndpointCache :=
  { input := (93/32), certificate := { exponent := 1, mantissa := (93/64) }, enclosure := { lower := (199502267867065215147087181980481593467718976/186998853330584474277627150744392851829513265), upper := (791625011825049392170963687645023543399626007923/742011450015759193933624534153750836059508635520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint471_valid : endpoint471.Valid 8 := by
  constructor
  · norm_num [endpoint471, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint471, EndpointCache.Valid,
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

theorem endpoint471PositiveFacts : PositiveEndpointFacts 8
    endpoint471 :=
  { valid := endpoint471_valid
    positive := by
      norm_num [endpoint471] }

noncomputable def endpoint472 : EndpointCache :=
  { input := (189/64), certificate := { exponent := 1, mantissa := (189/128) }, enclosure := { lower := (1530512828814249555215918002018261997622167080000/1413393488729073371934871140386320172812712708253), upper := (391811290481075634837910658113923392970316608819625/361828733114642783215327011938897964240054453312768) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint472_valid : endpoint472.Valid 8 := by
  constructor
  · norm_num [endpoint472, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint472, EndpointCache.Valid,
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

theorem endpoint472PositiveFacts : PositiveEndpointFacts 8
    endpoint472 :=
  { valid := endpoint472_valid
    positive := by
      norm_num [endpoint472] }

noncomputable def endpoint473 : EndpointCache :=
  { input := (337/128), certificate := { exponent := 1, mantissa := (337/256) }, enclosure := { lower := (7476026940248892518758300140365771103135788182869184/7722748159571777147200989793639104447545175838914135), upper := (1289943615594605830184071691206301074368810946623349605431/1332513858445152716086647582953665637797234819949600509440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint473_valid : endpoint473.Valid 8 := by
  constructor
  · norm_num [endpoint473, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint473, EndpointCache.Valid,
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

theorem endpoint473PositiveFacts : PositiveEndpointFacts 8
    endpoint473 :=
  { valid := endpoint473_valid
    positive := by
      norm_num [endpoint473] }

noncomputable def endpoint474 : EndpointCache :=
  { input := (317/128), certificate := { exponent := 1, mantissa := (317/256) }, enclosure := { lower := (16979645538592107058483046818186016091869888/18723320085694659921316797893219736822931695), upper := (2755864442441667862946590328868017581588418643047/3038869743188586083869401565261136165309105825280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint474_valid : endpoint474.Valid 8 := by
  constructor
  · norm_num [endpoint474, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint474, EndpointCache.Valid,
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

theorem endpoint474PositiveFacts : PositiveEndpointFacts 8
    endpoint474 :=
  { valid := endpoint474_valid
    positive := by
      norm_num [endpoint474] }

noncomputable def endpoint475 : EndpointCache :=
  { input := (321/128), certificate := { exponent := 1, mantissa := (321/256) }, enclosure := { lower := (51819233310253713844276958859692034356708887554484288/56361345798958373169438410517778443183956107102746765), upper := (2838864931465719859554900861873587102213615574455256151087/3087699968250135515714513881805974231389851371516878773760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint475_valid : endpoint475.Valid 8 := by
  constructor
  · norm_num [endpoint475, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint475, EndpointCache.Valid,
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

theorem endpoint475PositiveFacts : PositiveEndpointFacts 8
    endpoint475 :=
  { valid := endpoint475_valid
    positive := by
      norm_num [endpoint475] }

noncomputable def endpoint476 : EndpointCache :=
  { input := (663/256), certificate := { exponent := 1, mantissa := (663/512) }, enclosure := { lower := (209398122833026413341270548380125384968028429651063573824/220049036486564579674605792095733680762350559234619140625), upper := (3645202589017841828947804669323579865377335780814594174989687/3830613627158116202975537628802531914710998535156250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint476_valid : endpoint476.Valid 8 := by
  constructor
  · norm_num [endpoint476, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint476, EndpointCache.Valid,
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

theorem endpoint476PositiveFacts : PositiveEndpointFacts 8
    endpoint476 :=
  { valid := endpoint476_valid
    positive := by
      norm_num [endpoint476] }

noncomputable def endpoint477 : EndpointCache :=
  { input := (631/256), certificate := { exponent := 1, mantissa := (631/512) }, enclosure := { lower := (20114866355810062489303360465366786256069690920000/22297120870649167458116638073258696642627978339421), upper := (12997100457623316418295505646162290091491364766164982125/14407150867844735658057316991207667283454212436146842624) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint477_valid : endpoint477.Valid 8 := by
  constructor
  · norm_num [endpoint477, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint477, EndpointCache.Valid,
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

theorem endpoint477PositiveFacts : PositiveEndpointFacts 8
    endpoint477 :=
  { valid := endpoint477_valid
    positive := by
      norm_num [endpoint477] }

noncomputable def endpoint478 : EndpointCache :=
  { input := (323/128), certificate := { exponent := 1, mantissa := (323/256) }, enclosure := { lower := (58914762523430567453888772549535192702580800/63648831610803522778753530983272719029387469), upper := (9743087950468427036255734161899783693403651314485/10525989176468243383059143939889709182203982073344) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint478_valid : endpoint478.Valid 8 := by
  constructor
  · norm_num [endpoint478, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint478, EndpointCache.Valid,
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

theorem endpoint478PositiveFacts : PositiveEndpointFacts 8
    endpoint478 :=
  { valid := endpoint478_valid
    positive := by
      norm_num [endpoint478] }

noncomputable def endpoint479 : EndpointCache :=
  { input := (683/256), certificate := { exponent := 1, mantissa := (683/512) }, enclosure := { lower := (437093353211335034504504186033977466246993416931633426752/445414854500803019954290693678746657705918227691650390625), upper := (305699599916768736037718751767906147179964741529366248373034649/311519585919025625731871276833365982426257561101718750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint479_valid : endpoint479.Valid 8 := by
  constructor
  · norm_num [endpoint479, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint479, EndpointCache.Valid,
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

theorem endpoint479PositiveFacts : PositiveEndpointFacts 8
    endpoint479 :=
  { valid := endpoint479_valid
    positive := by
      norm_num [endpoint479] }

noncomputable def endpoint480 : EndpointCache :=
  { input := (715/256), certificate := { exponent := 1, mantissa := (715/512) }, enclosure := { lower := (2457394565140698814077827948909568800426242415552/2392544416178324703802738759404216739500196722627), upper := (967835414380736506139272850109826870204660846593913/942294416217924806420770957549968438941615939988480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint480_valid : endpoint480.Valid 8 := by
  constructor
  · norm_num [endpoint480, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint480, EndpointCache.Valid,
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

theorem endpoint480PositiveFacts : PositiveEndpointFacts 8
    endpoint480 :=
  { valid := endpoint480_valid
    positive := by
      norm_num [endpoint480] }

noncomputable def endpoint481 : EndpointCache :=
  { input := (95/32), certificate := { exponent := 1, mantissa := (95/64) }, enclosure := { lower := (54432316483897741586809581390361024/50023220423392691940467201599133019), upper := (661896979043332316328013456008137807611/608282360348455133996081171445457511040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint481_valid : endpoint481.Valid 8 := by
  constructor
  · norm_num [endpoint481, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint481, EndpointCache.Valid,
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

theorem endpoint481PositiveFacts : PositiveEndpointFacts 8
    endpoint481 :=
  { valid := endpoint481_valid
    positive := by
      norm_num [endpoint481] }

noncomputable def endpoint482 : EndpointCache :=
  { input := (49/16), certificate := { exponent := 1, mantissa := (49/32) }, enclosure := { lower := (64763138671765050508072140913216/57863931045670117797011901319365), upper := (29013886576767381056175610646677123/25923041108460212773061331791075520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint482_valid : endpoint482.Valid 8 := by
  constructor
  · norm_num [endpoint482, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint482, EndpointCache.Valid,
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

theorem endpoint482PositiveFacts : PositiveEndpointFacts 8
    endpoint482 :=
  { valid := endpoint482_valid
    positive := by
      norm_num [endpoint482] }

noncomputable def endpoint483 : EndpointCache :=
  { input := (25/8), certificate := { exponent := 1, mantissa := (25/16) }, enclosure := { lower := (76352152614210586856684874645096256/67008825176303860660755413796648321), upper := (61081723026079133354945113437129784649/53607060141043088528604331037318656800) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint483_valid : endpoint483.Valid 8 := by
  constructor
  · norm_num [endpoint483, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint483, EndpointCache.Valid,
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

theorem endpoint483PositiveFacts : PositiveEndpointFacts 8
    endpoint483 :=
  { valid := endpoint483_valid
    positive := by
      norm_num [endpoint483] }

noncomputable def endpoint484 : EndpointCache :=
  { input := (51/16), certificate := { exponent := 1, mantissa := (51/32) }, enclosure := { lower := (436133753374828667771520036795734017600/376224868110663973132140818144764420821), upper := (474513530814832918968529396153755846693455/409332656504402402767769210141503689853248) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint484_valid : endpoint484.Valid 8 := by
  constructor
  · norm_num [endpoint484, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint484, EndpointCache.Valid,
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

theorem endpoint484PositiveFacts : PositiveEndpointFacts 8
    endpoint484 :=
  { valid := endpoint484_valid
    positive := by
      norm_num [endpoint484] }

noncomputable def endpoint485 : EndpointCache :=
  { input := (13/4), certificate := { exponent := 1, mantissa := (13/8) }, enclosure := { lower := (19136429476697707155776/16235819262270150948405), upper := (43740410881022739611243/37110444028046059310640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint485_valid : endpoint485.Valid 8 := by
  constructor
  · norm_num [endpoint485, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint485, EndpointCache.Valid,
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

theorem endpoint485PositiveFacts : PositiveEndpointFacts 8
    endpoint485 :=
  { valid := endpoint485_valid
    positive := by
      norm_num [endpoint485] }

noncomputable def endpoint486 : EndpointCache :=
  { input := (53/16), certificate := { exponent := 1, mantissa := (53/32) }, enclosure := { lower := (22541211266023779347727207511293259027264/18820365052611386241434847679595947265625), upper := (76459789733081973802383813906800464821505793/63838678258457822130947003329189453125000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint486_valid : endpoint486.Valid 8 := by
  constructor
  · norm_num [endpoint486, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint486, EndpointCache.Valid,
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

theorem endpoint486PositiveFacts : PositiveEndpointFacts 8
    endpoint486 :=
  { valid := endpoint486_valid
    positive := by
      norm_num [endpoint486] }

noncomputable def endpoint487 : EndpointCache :=
  { input := (27/8), certificate := { exponent := 1, mantissa := (27/16) }, enclosure := { lower := (832617879767257341638197236752953024/684496120477532061442721474183421735), upper := (26643772538215185615277233797265528773/21903875855281025966167087173869495520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint487_valid : endpoint487.Valid 8 := by
  constructor
  · norm_num [endpoint487, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint487, EndpointCache.Valid,
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

theorem endpoint487PositiveFacts : PositiveEndpointFacts 8
    endpoint487 :=
  { valid := endpoint487_valid
    positive := by
      norm_num [endpoint487] }

noncomputable def endpoint488 : EndpointCache :=
  { input := (55/16), certificate := { exponent := 1, mantissa := (55/32) }, enclosure := { lower := (35316516209241964125450020088128/28602287596513281861677588523633), upper := (11301285349386887406532377244386643/9152732030884250195736828327562560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint488_valid : endpoint488.Valid 8 := by
  constructor
  · norm_num [endpoint488, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint488, EndpointCache.Valid,
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

theorem endpoint488PositiveFacts : PositiveEndpointFacts 8
    endpoint488 :=
  { valid := endpoint488_valid
    positive := by
      norm_num [endpoint488] }

noncomputable def endpoint489 : EndpointCache :=
  { input := (7/2), certificate := { exponent := 1, mantissa := (7/4) }, enclosure := { lower := (20499376505536114727115200/16363332121190259808363761), upper := (163995014397334205683088845/130906656969522078466910088) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint489_valid : endpoint489.Valid 8 := by
  constructor
  · norm_num [endpoint489, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint489, EndpointCache.Valid,
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

theorem endpoint489PositiveFacts : PositiveEndpointFacts 8
    endpoint489 :=
  { valid := endpoint489_valid
    positive := by
      norm_num [endpoint489] }

noncomputable def endpoint490 : EndpointCache :=
  { input := (183/64), certificate := { exponent := 1, mantissa := (183/128) }, enclosure := { lower := (796325490204863106192460166853774735527717300288/757969888061090199224120323258351920202168482765), upper := (12435419061268871941883883469551064039913902681392863/11836457771961984551083862968002423585877063026858240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint490_valid : endpoint490.Valid 8 := by
  constructor
  · norm_num [endpoint490, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint490, EndpointCache.Valid,
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

theorem endpoint490PositiveFacts : PositiveEndpointFacts 8
    endpoint490 :=
  { valid := endpoint490_valid
    positive := by
      norm_num [endpoint490] }

noncomputable def endpoint491 : EndpointCache :=
  { input := (193/64), certificate := { exponent := 1, mantissa := (193/128) }, enclosure := { lower := (656136212918852422823121109388579174250688/594430141121682460555075934866530434967015), upper := (32418378519698312884461982021394381346189086119/29369604412540087011105191789885535730850277120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint491_valid : endpoint491.Valid 8 := by
  constructor
  · norm_num [endpoint491, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint491, EndpointCache.Valid,
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

theorem endpoint491PositiveFacts : PositiveEndpointFacts 8
    endpoint491 :=
  { valid := endpoint491_valid
    positive := by
      norm_num [endpoint491] }

noncomputable def endpoint492 : EndpointCache :=
  { input := (101/32), certificate := { exponent := 1, mantissa := (101/64) }, enclosure := { lower := (2869836755062005321470880932695878976/2496846331968728608453943023681640625), upper := (37101250132463459738024107305136171443433/32279229379691723450092575410156250000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint492_valid : endpoint492.Valid 8 := by
  constructor
  · norm_num [endpoint492, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint492, EndpointCache.Valid,
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

theorem endpoint492PositiveFacts : PositiveEndpointFacts 8
    endpoint492 :=
  { valid := endpoint492_valid
    positive := by
      norm_num [endpoint492] }

noncomputable def endpoint493 : EndpointCache :=
  { input := (195/64), certificate := { exponent := 1, mantissa := (195/128) }, enclosure := { lower := (2086135838529927073130849757288131789975304713152/1872457581280033151631941776462650899840846802147), upper := (2670253915088845129093055558345578147565137342121933/2396745704038442434088885473872193151796283906748160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint493_valid : endpoint493.Valid 8 := by
  constructor
  · norm_num [endpoint493, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint493, EndpointCache.Valid,
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

theorem endpoint493PositiveFacts : PositiveEndpointFacts 8
    endpoint493 :=
  { valid := endpoint493_valid
    positive := by
      norm_num [endpoint493] }

noncomputable def endpoint494 : EndpointCache :=
  { input := (205/64), certificate := { exponent := 1, mantissa := (205/128) }, enclosure := { lower := (240004374536397545500631739615065899792576/206166849692808797332786691278918406192871), upper := (12595429764533006844410534306659396202543565631/10819636271878605684024645558317637957001870080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint494_valid : endpoint494.Valid 8 := by
  constructor
  · norm_num [endpoint494, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint494, EndpointCache.Valid,
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

theorem endpoint494PositiveFacts : PositiveEndpointFacts 8
    endpoint494 :=
  { valid := endpoint494_valid
    positive := by
      norm_num [endpoint494] }

noncomputable def endpoint495 : EndpointCache :=
  { input := (107/32), certificate := { exponent := 1, mantissa := (107/64) }, enclosure := { lower := (11330203091220702125705792746991816000/9386355270252756392507122969362759153), upper := (155178463794813405906133005066632555652425/128555521781381751551777556188392349359488) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint495_valid : endpoint495.Valid 8 := by
  constructor
  · norm_num [endpoint495, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint495, EndpointCache.Valid,
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

theorem endpoint495PositiveFacts : PositiveEndpointFacts 8
    endpoint495 :=
  { valid := endpoint495_valid
    positive := by
      norm_num [endpoint495] }

noncomputable def endpoint496 : EndpointCache :=
  { input := (207/64), certificate := { exponent := 1, mantissa := (207/128) }, enclosure := { lower := (132827360424848118108563829181036167285340889152/113156687446748755199424148640176852569580078125), upper := (782087509820260229402785115640784467059972945031461/666266575686456670614209387193361307929687500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint496_valid : endpoint496.Valid 8 := by
  constructor
  · norm_num [endpoint496, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint496, EndpointCache.Valid,
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

theorem endpoint496PositiveFacts : PositiveEndpointFacts 8
    endpoint496 :=
  { valid := endpoint496_valid
    positive := by
      norm_num [endpoint496] }

noncomputable def endpoint497 : EndpointCache :=
  { input := (217/64), certificate := { exponent := 1, mantissa := (217/128) }, enclosure := { lower := (237842790974891196949105875650366369198272/194791164184481478201488777188568115234375), upper := (1887520416438905044619061040110805167877236337/1545862678968045011007014935768476562500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint497_valid : endpoint497.Valid 8 := by
  constructor
  · norm_num [endpoint497, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint497, EndpointCache.Valid,
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

theorem endpoint497PositiveFacts : PositiveEndpointFacts 8
    endpoint497 :=
  { valid := endpoint497_valid
    positive := by
      norm_num [endpoint497] }

noncomputable def endpoint498 : EndpointCache :=
  { input := (57/16), certificate := { exponent := 1, mantissa := (57/32) }, enclosure := { lower := (47660228789357953487699460239683045342784/37514076266611329317429990082759975450645), upper := (57954839044445672566418131221197109984821159/45617116740199376449994867940636130147984320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint498_valid : endpoint498.Valid 8 := by
  constructor
  · norm_num [endpoint498, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint498, EndpointCache.Valid,
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

theorem endpoint498PositiveFacts : PositiveEndpointFacts 8
    endpoint498 :=
  { valid := endpoint498_valid
    positive := by
      norm_num [endpoint498] }

noncomputable def endpoint499 : EndpointCache :=
  { input := (113/32), certificate := { exponent := 1, mantissa := (113/64) }, enclosure := { lower := (1226249559168962673106655019700084928/971939680609702072810287910902032295), upper := (17736473878785465545552489714352909616487/14058135540338730781128004343286995114880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint499_valid : endpoint499.Valid 8 := by
  constructor
  · norm_num [endpoint499, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint499, EndpointCache.Valid,
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

theorem endpoint499PositiveFacts : PositiveEndpointFacts 8
    endpoint499 :=
  { valid := endpoint499_valid
    positive := by
      norm_num [endpoint499] }

noncomputable def endpoint500 : EndpointCache :=
  { input := (29/8), certificate := { exponent := 1, mantissa := (29/16) }, enclosure := { lower := (17357282471365966233267698752/13477675730683047637939453125), upper := (16107558369896274420676253683141/12507283078073868208007812500000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint500_valid : endpoint500.Valid 8 := by
  constructor
  · norm_num [endpoint500, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint500, EndpointCache.Valid,
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

theorem endpoint500PositiveFacts : PositiveEndpointFacts 8
    endpoint500 :=
  { valid := endpoint500_valid
    positive := by
      norm_num [endpoint500] }

noncomputable def endpoint501 : EndpointCache :=
  { input := (59/16), certificate := { exponent := 1, mantissa := (59/32) }, enclosure := { lower := (750787607815674134526549960585907865152/575338782291697292856559488022357656405), upper := (404996292865994203571233249137068504272571/310354177419064139689481232396060358655040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint501_valid : endpoint501.Valid 8 := by
  constructor
  · norm_num [endpoint501, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint501, EndpointCache.Valid,
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

theorem endpoint501PositiveFacts : PositiveEndpointFacts 8
    endpoint501 :=
  { valid := endpoint501_valid
    positive := by
      norm_num [endpoint501] }

noncomputable def endpoint502 : EndpointCache :=
  { input := (15/4), certificate := { exponent := 1, mantissa := (15/8) }, enclosure := { lower := (1380543977223597545175479888192/1044477305672250939988317422877), upper := (110443519937473607810996143449739/83558184453780075199065393830160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint502_valid : endpoint502.Valid 8 := by
  constructor
  · norm_num [endpoint502, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint502, EndpointCache.Valid,
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

theorem endpoint502PositiveFacts : PositiveEndpointFacts 8
    endpoint502 :=
  { valid := endpoint502_valid
    positive := by
      norm_num [endpoint502] }

noncomputable def endpoint503 : EndpointCache :=
  { input := (61/16), certificate := { exponent := 1, mantissa := (61/32) }, enclosure := { lower := (150350787423874599143154673208000/112345854304555257003309496323519), upper := (586969484165940663125294867221617095/438598215204983723340920273647018176) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint503_valid : endpoint503.Valid 8 := by
  constructor
  · norm_num [endpoint503, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint503, EndpointCache.Valid,
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

theorem endpoint503PositiveFacts : PositiveEndpointFacts 8
    endpoint503 :=
  { valid := endpoint503_valid
    positive := by
      norm_num [endpoint503] }

noncomputable def endpoint504 : EndpointCache :=
  { input := (31/8), certificate := { exponent := 1, mantissa := (31/16) }, enclosure := { lower := (3520510759118291605779306203518935488/2599034391871790436009650046544216515), upper := (3492346739193216069675693401514519711931/2578242116736816112521572846171862782880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint504_valid : endpoint504.Valid 8 := by
  constructor
  · norm_num [endpoint504, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint504, EndpointCache.Valid,
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

theorem endpoint504PositiveFacts : PositiveEndpointFacts 8
    endpoint504 :=
  { valid := endpoint504_valid
    positive := by
      norm_num [endpoint504] }

noncomputable def endpoint505 : EndpointCache :=
  { input := (63/16), certificate := { exponent := 1, mantissa := (63/32) }, enclosure := { lower := (136801813276902719713537987955159521532864/99815557473800611330510850002899169921875), upper := (1250759462591466210206266717098346256632283/912599382617605589307527771455078125000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint505_valid : endpoint505.Valid 8 := by
  constructor
  · norm_num [endpoint505, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint505, EndpointCache.Valid,
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

theorem endpoint505PositiveFacts : PositiveEndpointFacts 8
    endpoint505 :=
  { valid := endpoint505_valid
    positive := by
      norm_num [endpoint505] }

noncomputable def endpoint506 : EndpointCache :=
  { input := (4), certificate := { exponent := 2, mantissa := (1) }, enclosure := { lower := (298675509632/215448838605), upper := (597351034279/430897677210) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint506_valid : endpoint506.Valid 8 := by
  constructor
  · norm_num [endpoint506, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint506, EndpointCache.Valid,
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

theorem endpoint506PositiveFacts : PositiveEndpointFacts 8
    endpoint506 :=
  { valid := endpoint506_valid
    positive := by
      norm_num [endpoint506] }

noncomputable def endpoint507 : EndpointCache :=
  { input := (2559/1024), certificate := { exponent := 1, mantissa := (2559/2048) }, enclosure := { lower := (352773058036714343330295887785850589656158946711812146678940177600/385165462010701995072409416221541395450659523396585437923918450903), upper := (1232549577644251978069434740422742384024416013344048892006783303949673885/1345724985733647572159550390423448823068313900881049102537123588588580864) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint507_valid : endpoint507.Valid 8 := by
  constructor
  · norm_num [endpoint507, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint507, EndpointCache.Valid,
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

theorem endpoint507PositiveFacts : PositiveEndpointFacts 8
    endpoint507 :=
  { valid := endpoint507_valid
    positive := by
      norm_num [endpoint507] }

noncomputable def endpoint508 : EndpointCache :=
  { input := (2617/1024), certificate := { exponent := 1, mantissa := (2617/2048) }, enclosure := { lower := (5627086724368150212937611646215424827037420729724022466624/5997030997300473129350272016520706110540522121124267578125), upper := (60318049202630364241121722693701230794528014216815721781184997373/64283566571255145183271575008193281602701502017463125000000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint508_valid : endpoint508.Valid 8 := by
  constructor
  · norm_num [endpoint508, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint508, EndpointCache.Valid,
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

theorem endpoint508PositiveFacts : PositiveEndpointFacts 8
    endpoint508 :=
  { valid := endpoint508_valid
    positive := by
      norm_num [endpoint508] }

noncomputable def endpoint509 : EndpointCache :=
  { input := (645/256), certificate := { exponent := 1, mantissa := (645/512) }, enclosure := { lower := (27298413347647757022330381735350279091038328801286908736/29541407604695518581261876341939924659506499298246218281), upper := (6010018795934015136318567314723708382911165501466604012922027/6503836298249765370850614695441493813036950885501887416744960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint509_valid : endpoint509.Valid 8 := by
  constructor
  · norm_num [endpoint509, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint509, EndpointCache.Valid,
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

theorem endpoint509PositiveFacts : PositiveEndpointFacts 8
    endpoint509 :=
  { valid := endpoint509_valid
    positive := by
      norm_num [endpoint509] }

noncomputable def endpoint510 : EndpointCache :=
  { input := (327/128), certificate := { exponent := 1, mantissa := (327/256) }, enclosure := { lower := (5612420175383599797950980332758762161009053479921984/5983837533790564505643445478628910331943466962392385), upper := (313217950966125949134805623992114547740131886461254022267/333946005085783823930949405271322227805101004237194222080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint510_valid : endpoint510.Valid 8 := by
  constructor
  · norm_num [endpoint510, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint510, EndpointCache.Valid,
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

theorem endpoint510PositiveFacts : PositiveEndpointFacts 8
    endpoint510 :=
  { valid := endpoint510_valid
    positive := by
      norm_num [endpoint510] }

noncomputable def endpoint511 : EndpointCache :=
  { input := (1337/512), certificate := { exponent := 1, mantissa := (1337/1024) }, enclosure := { lower := (103468909623437959778867751249406238231231019879176000/107795952217951797619636220733248145117977421478888473), upper := (40473727174242041191756949772093679901240625399073165897775/42166327037191768771277861191783210429508992005053846206464) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint511_valid : endpoint511.Valid 8 := by
  constructor
  · norm_num [endpoint511, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint511, EndpointCache.Valid,
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

theorem endpoint511PositiveFacts : PositiveEndpointFacts 8
    endpoint511 :=
  { valid := endpoint511_valid
    positive := by
      norm_num [endpoint511] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
