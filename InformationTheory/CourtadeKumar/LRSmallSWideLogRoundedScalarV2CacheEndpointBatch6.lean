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

noncomputable def endpoint384 : EndpointCache :=
  { input := (2325/1024), certificate := { exponent := 1, mantissa := (2325/2048) }, enclosure := { lower := (144504717495690191226298831023814932418358120415897897564788080192/176224510608693412392842218452582539534689262357872131866424971397), upper := (458715784964829364981297572412594143982934518130585262921123745031427679/559407086476236368299838338255878013498917594428829295396779429202636800) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint384_valid : endpoint384.Valid 8 := by
  constructor
  · norm_num [endpoint384, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint384, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint384PositiveFacts : PositiveEndpointFacts 8
    endpoint384 :=
  { valid := endpoint384_valid
    positive := by
      norm_num [endpoint384] }

noncomputable def endpoint385 : EndpointCache :=
  { input := (9237/4096), certificate := { exponent := 1, mantissa := (9237/8192) }, enclosure := { lower := (728839537284484403984418469195873530398257750797705184107182686089822795584/896254204120701045400384269496864388473849766068703848984537373906460341145), upper := (36767284975676037496032972649891321226140493624394336107303181524984822402747525339/45212740722485469491819039388153371887386352512623233450367231168642930940075294720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint385_valid : endpoint385.Valid 8 := by
  constructor
  · norm_num [endpoint385, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint385, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint385PositiveFacts : PositiveEndpointFacts 8
    endpoint385 :=
  { valid := endpoint385_valid
    positive := by
      norm_num [endpoint385] }

noncomputable def endpoint386 : EndpointCache :=
  { input := (4671/2048), certificate := { exponent := 1, mantissa := (4671/4096) }, enclosure := { lower := (2243428436154251408392429789513783824112838276033415003095467927347008/2720924996884311034389087435770053555055588894290762694914855032743865), upper := (3179422741758013079871852523571888233649727981841900864032736931843478829883/3856138440384395746912764939372292219081661470411177543436451190085129379840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint386_valid : endpoint386.Valid 8 := by
  constructor
  · norm_num [endpoint386, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint386, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint386PositiveFacts : PositiveEndpointFacts 8
    endpoint386 :=
  { valid := endpoint386_valid
    positive := by
      norm_num [endpoint386] }

noncomputable def endpoint387 : EndpointCache :=
  { input := (289/128), certificate := { exponent := 1, mantissa := (289/256) }, enclosure := { lower := (2786310483887304644101375024437184196789301728214464/3421319647996128316723213483187088934684295654296875), upper := (412284798500122198160839261052235194711229954156764080747/506245825674691114768900452680227175487365859375000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint387_valid : endpoint387.Valid 8 := by
  constructor
  · norm_num [endpoint387, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint387, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint387PositiveFacts : PositiveEndpointFacts 8
    endpoint387 :=
  { valid := endpoint387_valid
    positive := by
      norm_num [endpoint387] }

noncomputable def endpoint388 : EndpointCache :=
  { input := (585/256), certificate := { exponent := 1, mantissa := (585/512) }, enclosure := { lower := (20397827453343681837769463996768550095156369624287163584/24681725991056175538412060805615464409925993351994261079), upper := (104436878762862910519511482405571144140053641897677368320267/126370437074207618756669751324751177778821085962210616724480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint388_valid : endpoint388.Valid 8 := by
  constructor
  · norm_num [endpoint388, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint388, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint388PositiveFacts : PositiveEndpointFacts 8
    endpoint388 :=
  { valid := endpoint388_valid
    positive := by
      norm_num [endpoint388] }

noncomputable def endpoint389 : EndpointCache :=
  { input := (291/128), certificate := { exponent := 1, mantissa := (291/256) }, enclosure := { lower := (20780317308523937056627715532894652208546184207940288/25301953446386643686766181163060449022336704202304015), upper := (1032033700704120523004038061657895901109861521534346541677/1256596215961346272059555621282234140245330077503226600960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint389_valid : endpoint389.Valid 8 := by
  constructor
  · norm_num [endpoint389, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint389, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint389PositiveFacts : PositiveEndpointFacts 8
    endpoint389 :=
  { valid := endpoint389_valid
    positive := by
      norm_num [endpoint389] }

noncomputable def endpoint390 : EndpointCache :=
  { input := (589/256), certificate := { exponent := 1, mantissa := (589/512) }, enclosure := { lower := (5886637277821755747733225844306024535095414742464/7064681898971138043831506966671758829773830945835), upper := (3550442935434778998157442450855922199275919591574587619/4260963981817856315204359785850537933554469301347138560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint390_valid : endpoint390.Valid 8 := by
  constructor
  · norm_num [endpoint390, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint390, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint390PositiveFacts : PositiveEndpointFacts 8
    endpoint390 :=
  { valid := endpoint390_valid
    positive := by
      norm_num [endpoint390] }

noncomputable def endpoint391 : EndpointCache :=
  { input := (9341/4096), certificate := { exponent := 1, mantissa := (9341/8192) }, enclosure := { lower := (161568578952690680124025115220588084318568738466508896757071456163980840000/195982658737185060100035041154965157327272226757271639042115795610679963997), upper := (24726931503395448067898883448979697554251197764949744659732937608504819261658946885/29993763066086123870526297201517027894788913072368425046710741349160739531914887168) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint391_valid : endpoint391.Valid 8 := by
  constructor
  · norm_num [endpoint391, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint391, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint391PositiveFacts : PositiveEndpointFacts 8
    endpoint391 :=
  { valid := endpoint391_valid
    positive := by
      norm_num [endpoint391] }

noncomputable def endpoint392 : EndpointCache :=
  { input := (9447/4096), certificate := { exponent := 1, mantissa := (9447/8192) }, enclosure := { lower := (896389715540869784213950205220232928748063311558345299278108550981496667584/1072638944121952133772222338588793668993150979293118530173946605844806804395), upper := (46247629178279143222263845398662749715223271007851853887212462321204860330681287209/55340892734095806779371161914836766943796140995281391640866944807817979937420984320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint392_valid : endpoint392.Valid 8 := by
  constructor
  · norm_num [endpoint392, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint392, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint392PositiveFacts : PositiveEndpointFacts 8
    endpoint392 :=
  { valid := endpoint392_valid
    positive := by
      norm_num [endpoint392] }

noncomputable def endpoint393 : EndpointCache :=
  { input := (587/256), certificate := { exponent := 1, mantissa := (587/512) }, enclosure := { lower := (105247000602484004853399415997409303209042486915440597312/126826936925108460177743485710174657724642838056306841985), upper := (9037530060909735755255171762804781536850026598078632120609663/10890592837491370587331353762651066380341444891655623862154240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint393_valid : endpoint393.Valid 8 := by
  constructor
  · norm_num [endpoint393, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint393, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint393PositiveFacts : PositiveEndpointFacts 8
    endpoint393 :=
  { valid := endpoint393_valid
    positive := by
      norm_num [endpoint393] }

noncomputable def endpoint394 : EndpointCache :=
  { input := (595/256), certificate := { exponent := 1, mantissa := (595/512) }, enclosure := { lower := (11635766098041653332794169356032336513180181692224/13796522875881619741525184229400179777028338934329), upper := (1012777102095859504063801573014027291907910904251417047/1200849351116736182302352035326991647792546620843996160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint394_valid : endpoint394.Valid 8 := by
  constructor
  · norm_num [endpoint394, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint394, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint394PositiveFacts : PositiveEndpointFacts 8
    endpoint394 :=
  { valid := endpoint394_valid
    positive := by
      norm_num [endpoint394] }

noncomputable def endpoint395 : EndpointCache :=
  { input := (295/128), certificate := { exponent := 1, mantissa := (295/256) }, enclosure := { lower := (4713093457713898116097082468288955176888523244962496/5644794497519846005541720044401187240942289906103471), upper := (711865650707718761525549668444532939556348208895223862079/852589760905397540677021395506355320871923467417868259840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint395_valid : endpoint395.Valid 8 := by
  constructor
  · norm_num [endpoint395, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint395, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint395PositiveFacts : PositiveEndpointFacts 8
    endpoint395 :=
  { valid := endpoint395_valid
    positive := by
      norm_num [endpoint395] }

noncomputable def endpoint396 : EndpointCache :=
  { input := (597/256), certificate := { exponent := 1, mantissa := (597/512) }, enclosure := { lower := (78284281584231910242238132358494833864362431358441143744/92453778359364409968974314988899247939248472170697505195), upper := (15952458092354020641614530254489049292884234694592085093023409/18839861138957842005837710011177933148068296665056054818616320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint396_valid : endpoint396.Valid 8 := by
  constructor
  · norm_num [endpoint396, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint396, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint396PositiveFacts : PositiveEndpointFacts 8
    endpoint396 :=
  { valid := endpoint396_valid
    positive := by
      norm_num [endpoint396] }

noncomputable def endpoint397 : EndpointCache :=
  { input := (593/256), certificate := { exponent := 1, mantissa := (593/512) }, enclosure := { lower := (62247659483180851021793169532485814367939340109567198528/74102860928392229026415041443099862304394167633056640625), upper := (37798771547281398118313049779647125117558405146315959732241681/44997628447269470016168058445576415586821879200156250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint397_valid : endpoint397.Valid 8 := by
  constructor
  · norm_num [endpoint397, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint397, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint397PositiveFacts : PositiveEndpointFacts 8
    endpoint397 :=
  { valid := endpoint397_valid
    positive := by
      norm_num [endpoint397] }

noncomputable def endpoint398 : EndpointCache :=
  { input := (297/128), certificate := { exponent := 1, mantissa := (297/256) }, enclosure := { lower := (275637326327191766436035260081400512916929266806464/327476194224693218831678974432083600200223291538335), upper := (20160902000112385759427209722827974598288967523039889/23952544491863275434545662129889543328930617895375360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint398_valid : endpoint398.Valid 8 := by
  constructor
  · norm_num [endpoint398, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint398, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint398PositiveFacts : PositiveEndpointFacts 8
    endpoint398 :=
  { valid := endpoint398_valid
    positive := by
      norm_num [endpoint398] }

noncomputable def endpoint399 : EndpointCache :=
  { input := (601/256), certificate := { exponent := 1, mantissa := (601/512) }, enclosure := { lower := (1824090139982451293457894386951139259248922856000/2137394842969443518769443228599629658950132971253), upper := (160369839032393310678559471864332818555093258885226995/187914869119946686870737975645385497604246661957200896) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint399_valid : endpoint399.Valid 8 := by
  constructor
  · norm_num [endpoint399, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint399, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint399PositiveFacts : PositiveEndpointFacts 8
    endpoint399 :=
  { valid := endpoint399_valid
    positive := by
      norm_num [endpoint399] }

noncomputable def endpoint400 : EndpointCache :=
  { input := (299/128), certificate := { exponent := 1, mantissa := (299/256) }, enclosure := { lower := (206673619934992054543447630631301116217260096/243600162649842122442210696104845733642578125), upper := (2433788598334501767444525034843830449861914274681/2868635515364540833879473157330663359375000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint400_valid : endpoint400.Valid 8 := by
  constructor
  · norm_num [endpoint400, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint400, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint400PositiveFacts : PositiveEndpointFacts 8
    endpoint400 :=
  { valid := endpoint400_valid
    positive := by
      norm_num [endpoint400] }

noncomputable def endpoint401 : EndpointCache :=
  { input := (609/256), certificate := { exponent := 1, mantissa := (609/512) }, enclosure := { lower := (1035779922507310880448775362889989742225228958822522503232/1195166320293657947836950234422298020963833799947034362605), upper := (30758521197145789599932872912906780219941247992268857681929017/35491659047440466418966074161404562030542008523227132431918080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint401_valid : endpoint401.Valid 8 := by
  constructor
  · norm_num [endpoint401, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint401, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint401PositiveFacts : PositiveEndpointFacts 8
    endpoint401 :=
  { valid := endpoint401_valid
    positive := by
      norm_num [endpoint401] }

noncomputable def endpoint402 : EndpointCache :=
  { input := (613/256), certificate := { exponent := 1, mantissa := (613/512) }, enclosure := { lower := (10960304968343926442169721350559373322531473385536/12552063661332286557126280968077480792999267578125), upper := (6879915089565778017314971182536970701522507980802422277/7879080984982212259346852079033851623535156250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint402_valid : endpoint402.Valid 8 := by
  constructor
  · norm_num [endpoint402, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint402, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint402PositiveFacts : PositiveEndpointFacts 8
    endpoint402 :=
  { valid := endpoint402_valid
    positive := by
      norm_num [endpoint402] }

noncomputable def endpoint403 : EndpointCache :=
  { input := (157/64), certificate := { exponent := 1, mantissa := (157/128) }, enclosure := { lower := (89570760250519078020534475509505456627648/99815557473800611330510850002899169921875), upper := (3600028065885944356655100266326858710197635051/4011786885986994170595892083316523437500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint403_valid : endpoint403.Valid 8 := by
  constructor
  · norm_num [endpoint403, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint403, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint403PositiveFacts : PositiveEndpointFacts 8
    endpoint403 :=
  { valid := endpoint403_valid
    positive := by
      norm_num [endpoint403] }

noncomputable def endpoint404 : EndpointCache :=
  { input := (2387/1024), certificate := { exponent := 1, mantissa := (2387/2048) }, enclosure := { lower := (921050716251087330251825554359409107133740974162049890817454534336/1088299726039424059195662018403457759332532396721843979339599609375), upper := (116951338154336953564864906744595714617602799956488355954028494178906771/138187946013581909340428380448797452449007633606152861120625000000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint404_valid : endpoint404.Valid 8 := by
  constructor
  · norm_num [endpoint404, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint404, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint404PositiveFacts : PositiveEndpointFacts 8
    endpoint404 :=
  { valid := endpoint404_valid
    positive := by
      norm_num [endpoint404] }

noncomputable def endpoint405 : EndpointCache :=
  { input := (2415/1024), certificate := { exponent := 1, mantissa := (2415/2048) }, enclosure := { lower := (15787474584254052972735924815993432465606613123670372793393650624/18400689768993634356508673633961664746831327272171587323166055619), upper := (1062361739882798922644433627997921504105596932766227367311363535353137/1238208701255251646755692232648757508906775485469100641814876976967680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint405_valid : endpoint405.Valid 8 := by
  constructor
  · norm_num [endpoint405, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint405, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint405PositiveFacts : PositiveEndpointFacts 8
    endpoint405 :=
  { valid := endpoint405_valid
    positive := by
      norm_num [endpoint405] }

noncomputable def endpoint406 : EndpointCache :=
  { input := (1207/512), certificate := { exponent := 1, mantissa := (1207/1024) }, enclosure := { lower := (6239310165889189629108359618034217700667484449295907508817600/7275581454276770375763131229107813663425314938913854145664671), upper := (15423175727574875767519359284776697430157176840219133231853141750735/17984771717759102655582411557955852475912919308838956961417744173056) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint406_valid : endpoint406.Valid 8 := by
  constructor
  · norm_num [endpoint406, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint406, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint406PositiveFacts : PositiveEndpointFacts 8
    endpoint406 :=
  { valid := endpoint406_valid
    positive := by
      norm_num [endpoint406] }

noncomputable def endpoint407 : EndpointCache :=
  { input := (1221/512), certificate := { exponent := 1, mantissa := (1221/1024) }, enclosure := { lower := (34726379827112102585584563030850425200864614441559255727237952/39956674653635781625856927259499567218232054551930084228515625), upper := (239220564593785828578529378022090010497308904322674361183083333827/275250634413991362589175865455985382320795651429732187500000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint407_valid : endpoint407.Valid 8 := by
  constructor
  · norm_num [endpoint407, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint407, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint407PositiveFacts : PositiveEndpointFacts 8
    endpoint407 :=
  { valid := endpoint407_valid
    positive := by
      norm_num [endpoint407] }

noncomputable def endpoint408 : EndpointCache :=
  { input := (607/256), certificate := { exponent := 1, mantissa := (607/512) }, enclosure := { lower := (199460584885973794793972998018774975929697003712/231030606380412668643176900183796846393865749735), upper := (123978319328359149589199585921702719217958364112822951/143601231946660341623202179493442238219342346331284480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint408_valid : endpoint408.Valid 8 := by
  constructor
  · norm_num [endpoint408, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint408, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint408PositiveFacts : PositiveEndpointFacts 8
    endpoint408 :=
  { valid := endpoint408_valid
    positive := by
      norm_num [endpoint408] }

noncomputable def endpoint409 : EndpointCache :=
  { input := (615/256), certificate := { exponent := 1, mantissa := (615/512) }, enclosure := { lower := (32423465645420690271047172687048959896539258544313706304/36994303371853549871459020374879385008981335416583088729), upper := (972333434798638483110640634306189690625487410076856250845029/1109406309117071027002382508156382928726480275807017426570240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint409_valid : endpoint409.Valid 8 := by
  constructor
  · norm_num [endpoint409, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint409, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint409PositiveFacts : PositiveEndpointFacts 8
    endpoint409 :=
  { valid := endpoint409_valid
    positive := by
      norm_num [endpoint409] }

noncomputable def endpoint410 : EndpointCache :=
  { input := (2441/1024), certificate := { exponent := 1, mantissa := (2441/2048) }, enclosure := { lower := (87198766193481520241554830626375676434987142515006075271181692736/100379467169804554123823872310615511265743087968050378455230044665), upper := (871842580674003217169869936987832854164863898132894251252217799346132681/1003627640264674986460176680182630248446684683182124948722550943855677440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint410_valid : endpoint410.Valid 8 := by
  constructor
  · norm_num [endpoint410, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint410, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint410PositiveFacts : PositiveEndpointFacts 8
    endpoint410 :=
  { valid := endpoint410_valid
    positive := by
      norm_num [endpoint410] }

noncomputable def endpoint411 : EndpointCache :=
  { input := (2469/1024), certificate := { exponent := 1, mantissa := (2469/2048) }, enclosure := { lower := (252148213492019590861909582679507292404090936443661651372307073600/286500583900305785271019167344119453624322981379198257105703275253), upper := (849993661694297758810770624096955256667024359373708644049037027689268495/965795760332602004594887781270365431123221764813128358289382586504065024) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint411_valid : endpoint411.Valid 8 := by
  constructor
  · norm_num [endpoint411, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint411, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint411PositiveFacts : PositiveEndpointFacts 8
    endpoint411 :=
  { valid := endpoint411_valid
    positive := by
      norm_num [endpoint411] }

noncomputable def endpoint412 : EndpointCache :=
  { input := (307/128), certificate := { exponent := 1, mantissa := (307/256) }, enclosure := { lower := (34110456660042181206547399191946513500498456269215424/38991512328360836663768388794026110382069370041932735), upper := (5361618126434452226733074032741786500216529672620932764951/6128841873821069750157770424200200134295191860671155018240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint412_valid : endpoint412.Valid 8 := by
  constructor
  · norm_num [endpoint412, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint412, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint412PositiveFacts : PositiveEndpointFacts 8
    endpoint412 :=
  { valid := endpoint412_valid
    positive := by
      norm_num [endpoint412] }

noncomputable def endpoint413 : EndpointCache :=
  { input := (311/128), certificate := { exponent := 1, mantissa := (311/256) }, enclosure := { lower := (383239308594465163871627925507143426412574912/431691184330087407535317355573480563703629735), upper := (8717708969107076436302639952741379617584940494257/9819864380464068296666236166096636731379481423360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint413_valid : endpoint413.Valid 8 := by
  constructor
  · norm_num [endpoint413, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint413, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint413PositiveFacts : PositiveEndpointFacts 8
    endpoint413 :=
  { valid := endpoint413_valid
    positive := by
      norm_num [endpoint413] }

noncomputable def endpoint414 : EndpointCache :=
  { input := (159/64), certificate := { exponent := 1, mantissa := (159/128) }, enclosure := { lower := (41357667241784107345697554584224295760838036800/45446931319074238557479464286775353885616536529), upper := (80162977125703268866853671901019434807739668435405/88089137733885609821125910206138285931435023946496) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint414_valid : endpoint414.Valid 8 := by
  constructor
  · norm_num [endpoint414, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint414, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint414PositiveFacts : PositiveEndpointFacts 8
    endpoint414 :=
  { valid := endpoint414_valid
    positive := by
      norm_num [endpoint414] }

noncomputable def endpoint415 : EndpointCache :=
  { input := (309/128), certificate := { exponent := 1, mantissa := (309/256) }, enclosure := { lower := (36240991538133182788429425627579681654334381334794048/41121682409562212505634505328000649606063385009765625), upper := (1911204967538236000393488029343321793853264463634237204283/2168593043550672838697141272977442257625358671875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint415_valid : endpoint415.Valid 8 := by
  constructor
  · norm_num [endpoint415, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint415, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint415PositiveFacts : PositiveEndpointFacts 8
    endpoint415 :=
  { valid := endpoint415_valid
    positive := by
      norm_num [endpoint415] }

noncomputable def endpoint416 : EndpointCache :=
  { input := (313/128), certificate := { exponent := 1, mantissa := (313/256) }, enclosure := { lower := (8174847594890154795904486677724497093220901501896000/9142356428790320550077859665263041513416265443257329), upper := (1310068401693355602862525699039212472458948968459687689505/1465117471852221610073277478516393980774037034874646516224) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint416_valid : endpoint416.Valid 8 := by
  constructor
  · norm_num [endpoint416, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint416, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint416PositiveFacts : PositiveEndpointFacts 8
    endpoint416 :=
  { valid := endpoint416_valid
    positive := by
      norm_num [endpoint416] }

noncomputable def endpoint417 : EndpointCache :=
  { input := (315/128), certificate := { exponent := 1, mantissa := (315/256) }, enclosure := { lower := (788909606273594723731556092242339841985841287008576/876038295524094401112007834376343757535249030200161), upper := (2019608631134076206735648195784105774928114349940484423/2242658036541681666846740056003440019290237517312412160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint417_valid : endpoint417.Valid 8 := by
  constructor
  · norm_num [endpoint417, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint417, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint417PositiveFacts : PositiveEndpointFacts 8
    endpoint417 :=
  { valid := endpoint417_valid
    positive := by
      norm_num [endpoint417] }

noncomputable def endpoint418 : EndpointCache :=
  { input := (303/128), certificate := { exponent := 1, mantissa := (303/256) }, enclosure := { lower := (66354021987781833753457804055706321929483641448000/77003396024886007697072956579897461566999393618469), upper := (3431299254410274126662475906470673723647932963979713175/3981999615238905230031036730659657532552672642798268928) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint418_valid : endpoint418.Valid 8 := by
  constructor
  · norm_num [endpoint418, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint418, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint418PositiveFacts : PositiveEndpointFacts 8
    endpoint418 :=
  { valid := endpoint418_valid
    positive := by
      norm_num [endpoint418] }

noncomputable def endpoint419 : EndpointCache :=
  { input := (161/64), certificate := { exponent := 1, mantissa := (161/128) }, enclosure := { lower := (1628501608566258312130344592183976353203860373568/1765272674776664606519915967619258716878039865645), upper := (9588617652330765900054093369339379568523759333945899/10393925509085001203189265217342195324977898728917760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint419_valid : endpoint419.Valid 8 := by
  constructor
  · norm_num [endpoint419, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint419, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint419PositiveFacts : PositiveEndpointFacts 8
    endpoint419 :=
  { valid := endpoint419_valid
    positive := by
      norm_num [endpoint419] }

noncomputable def endpoint420 : EndpointCache :=
  { input := (2395/1024), certificate := { exponent := 1, mantissa := (2395/2048) }, enclosure := { lower := (13241848970841425833501851881283396721332608839222982332736/15584756846940720515962796840645851877522217099278460765921), upper := (129901481719745145614670653143975464010093201370369062011166436921/152885217887940713003953759982988555250342747966553757836823736320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint420_valid : endpoint420.Valid 8 := by
  constructor
  · norm_num [endpoint420, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint420, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint420PositiveFacts : PositiveEndpointFacts 8
    endpoint420 :=
  { valid := endpoint420_valid
    positive := by
      norm_num [endpoint420] }

noncomputable def endpoint421 : EndpointCache :=
  { input := (2437/1024), certificate := { exponent := 1, mantissa := (2437/2048) }, enclosure := { lower := (664998939436510829209480169113304288275601362389602058944/766966130002850474151836051554835674399203473968505859375), upper := (6637987626892957154878971586885297579066068729932171776504110743/7655819095314213296160868178489895069740477915386875000000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint421_valid : endpoint421.Valid 8 := by
  constructor
  · norm_num [endpoint421, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint421, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint421PositiveFacts : PositiveEndpointFacts 8
    endpoint421 :=
  { valid := endpoint421_valid
    positive := by
      norm_num [endpoint421] }

noncomputable def endpoint422 : EndpointCache :=
  { input := (301/128), certificate := { exponent := 1, mantissa := (301/256) }, enclosure := { lower := (28390878649537436480105027842830290217784788782420288/33202599353972843521564389615107642190679045077383265), upper := (625053597084176288950961320868069649984092794987300774063/730988427377066122970761601766209850469989856423669962240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint422_valid : endpoint422.Valid 8 := by
  constructor
  · norm_num [endpoint422, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint422, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint422PositiveFacts : PositiveEndpointFacts 8
    endpoint422 :=
  { valid := endpoint422_valid
    positive := by
      norm_num [endpoint422] }

noncomputable def endpoint423 : EndpointCache :=
  { input := (617/256), certificate := { exponent := 1, mantissa := (617/512) }, enclosure := { lower := (1169724861456329724559582468177827039429321191502689349184/1329698828724802294211019006925037751510662298121897368645), upper := (739041539904254288641850693786766632649352352751532558455034517/840114357578959887900875496727294251706448525251799732688860160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint423_valid : endpoint423.Valid 8 := by
  constructor
  · norm_num [endpoint423, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint423, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint423PositiveFacts : PositiveEndpointFacts 8
    endpoint423 :=
  { valid := endpoint423_valid
    positive := by
      norm_num [endpoint423] }

noncomputable def endpoint424 : EndpointCache :=
  { input := (623/256), certificate := { exponent := 1, mantissa := (623/512) }, enclosure := { lower := (1280454360970966624029854788931839758043322267977587657664/1439733401371082730829243347381795312016352783660888671875), upper := (116695490927539529140505175965126310308966175633232836056268869/131211543267354995756853921706987297555922327291718750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint424_valid : endpoint424.Valid 8 := by
  constructor
  · norm_num [endpoint424, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint424, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint424PositiveFacts : PositiveEndpointFacts 8
    endpoint424 :=
  { valid := endpoint424_valid
    positive := by
      norm_num [endpoint424] }

noncomputable def endpoint425 : EndpointCache :=
  { input := (2461/1024), certificate := { exponent := 1, mantissa := (2461/2048) }, enclosure := { lower := (85242227217197489727825166463209596301071882506986420236224/97214011865614018277921290418026824027563753135159480417235), upper := (859263489432981222835077359799569981621395525219970901716158710059/979942126392426901430125755264057401064793687923210163432715612160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint425_valid : endpoint425.Valid 8 := by
  constructor
  · norm_num [endpoint425, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint425, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint425PositiveFacts : PositiveEndpointFacts 8
    endpoint425 :=
  { valid := endpoint425_valid
    positive := by
      norm_num [endpoint425] }

noncomputable def endpoint426 : EndpointCache :=
  { input := (2503/1024), certificate := { exponent := 1, mantissa := (2503/2048) }, enclosure := { lower := (99851670659029506966600032413149448996650492187792580231488/111719213374370823539199231784807371627443965283781734351265), upper := (1023708104833353038869517947556970177549358001637706166616457366609/1145377550647501501721049813636599198447584235951332069708661944320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint426_valid : endpoint426.Valid 8 := by
  constructor
  · norm_num [endpoint426, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint426, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint426PositiveFacts : PositiveEndpointFacts 8
    endpoint426 :=
  { valid := endpoint426_valid
    positive := by
      norm_num [endpoint426] }

noncomputable def endpoint427 : EndpointCache :=
  { input := (633/256), certificate := { exponent := 1, mantissa := (633/512) }, enclosure := { lower := (114359502204174703937567256338938371094718838419760235328/126323196085083799435546597525845203062920323638916015625), upper := (24708971959782423077387219670453450498358698818240939898083987/27293895038927546041241940047824217954586816806718750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint427_valid : endpoint427.Valid 8 := by
  constructor
  · norm_num [endpoint427, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint427, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint427PositiveFacts : PositiveEndpointFacts 8
    endpoint427 :=
  { valid := endpoint427_valid
    positive := by
      norm_num [endpoint427] }

noncomputable def endpoint428 : EndpointCache :=
  { input := (625/256), certificate := { exponent := 1, mantissa := (625/512) }, enclosure := { lower := (2043450511924797630692261155291910396210155130816/2289390061023529124692324439971914648707750933331), upper := (1307808353160115258392668085018254157900763326974260211/1465209639055058639803087641582025375172960597331840000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint428_valid : endpoint428.Valid 8 := by
  constructor
  · norm_num [endpoint428, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint428, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint428PositiveFacts : PositiveEndpointFacts 8
    endpoint428 :=
  { valid := endpoint428_valid
    positive := by
      norm_num [endpoint428] }

noncomputable def endpoint429 : EndpointCache :=
  { input := (637/256), certificate := { exponent := 1, mantissa := (637/512) }, enclosure := { lower := (109932567760722049740447419573971929830373054334912/120594018405407798365345943965237199060078179181235), upper := (787996660769548570397515312966037137745250905443554001/864417923929963098682799726342820242862640388371092480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint429_valid : endpoint429.Valid 8 := by
  constructor
  · norm_num [endpoint429, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint429, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint429PositiveFacts : PositiveEndpointFacts 8
    endpoint429 :=
  { valid := endpoint429_valid
    positive := by
      norm_num [endpoint429] }

noncomputable def endpoint430 : EndpointCache :=
  { input := (2515/1024), certificate := { exponent := 1, mantissa := (2515/2048) }, enclosure := { lower := (229517737058182271541701530219468987543827784442593149376/255429451897714462614614817642434322839073213763696132731), upper := (2364363243085442763956796914582096307442404439480930005175418611/2631291172957191673756697667054478630667342367193889889560432640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint430_valid : endpoint430.Valid 8 := by
  constructor
  · norm_num [endpoint430, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint430, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint430PositiveFacts : PositiveEndpointFacts 8
    endpoint430 :=
  { valid := endpoint430_valid
    positive := by
      norm_num [endpoint430] }

noncomputable def endpoint431 : EndpointCache :=
  { input := (1279/512), certificate := { exponent := 1, mantissa := (1279/1024) }, enclosure := { lower := (589351693442987465917793729144534856970975818834604579226432/643741984457260409529636922627695626811845538776010496344585), upper := (220534734338539703085896928130177812338542488665353953757950597487/240887514878781751234093531147943557615133387072224526577290741760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint431_valid : endpoint431.Valid 8 := by
  constructor
  · norm_num [endpoint431, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint431, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint431PositiveFacts : PositiveEndpointFacts 8
    endpoint431 :=
  { valid := endpoint431_valid
    positive := by
      norm_num [endpoint431] }

noncomputable def endpoint432 : EndpointCache :=
  { input := (629/256), certificate := { exponent := 1, mantissa := (629/512) }, enclosure := { lower := (200109709537989387745589263071675934819822492685561910976/222602882420425759220634410639495155464364892230160382015), upper := (18412837996091305549251006367923597065159415159351135156384833/20482518022209507115853391622179467379139367089411054487761920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint432_valid : endpoint432.Valid 8 := by
  constructor
  · norm_num [endpoint432, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint432, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint432PositiveFacts : PositiveEndpointFacts 8
    endpoint432 :=
  { valid := endpoint432_valid
    positive := by
      norm_num [endpoint432] }

noncomputable def endpoint433 : EndpointCache :=
  { input := (641/256), certificate := { exponent := 1, mantissa := (641/512) }, enclosure := { lower := (4346059834941453537226731775892988688200766120077121600/4735033296024682753553276048444597105907232796961242061), upper := (2852684192848679073252994363801973211889156936686075755733965/3108000094977865364508313545782258426763813092200607908967424) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint433_valid : endpoint433.Valid 8 := by
  constructor
  · norm_num [endpoint433, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint433, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint433PositiveFacts : PositiveEndpointFacts 8
    endpoint433 :=
  { valid := endpoint433_valid
    positive := by
      norm_num [endpoint433] }

noncomputable def endpoint434 : EndpointCache :=
  { input := (81/32), certificate := { exponent := 1, mantissa := (81/64) }, enclosure := { lower := (7527448500402209892472637324469116706521536/8105245072602902313271847333793182373046875), upper := (963513426127274062991537895014867794304432363/1037471369293171496098796458725527343750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint434_valid : endpoint434.Valid 8 := by
  constructor
  · norm_num [endpoint434, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint434, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint434PositiveFacts : PositiveEndpointFacts 8
    endpoint434 :=
  { valid := endpoint434_valid
    positive := by
      norm_num [endpoint434] }

noncomputable def endpoint435 : EndpointCache :=
  { input := (165/64), certificate := { exponent := 1, mantissa := (165/128) }, enclosure := { lower := (410929243112171581494077765557410154812395739712/433898809260548402759675458247441857649140980597), upper := (525989440860109517228723965595559360778706535330509/555390475853501955532384586556725577790900455164160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint435_valid : endpoint435.Valid 8 := by
  constructor
  · norm_num [endpoint435, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint435, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint435PositiveFacts : PositiveEndpointFacts 8
    endpoint435 :=
  { valid := endpoint435_valid
    positive := by
      norm_num [endpoint435] }

noncomputable def endpoint436 : EndpointCache :=
  { input := (83/32), certificate := { exponent := 1, mantissa := (83/64) }, enclosure := { lower := (661192518366103233263220350279858624/693724955507504299499293577587418235), upper := (1003501349075831266075277192471625714773/1052876275330246525411499281184104475520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint436_valid : endpoint436.Valid 8 := by
  constructor
  · norm_num [endpoint436, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint436, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint436PositiveFacts : PositiveEndpointFacts 8
    endpoint436 :=
  { valid := endpoint436_valid
    positive := by
      norm_num [endpoint436] }

noncomputable def endpoint437 : EndpointCache :=
  { input := (163/64), certificate := { exponent := 1, mantissa := (163/128) }, enclosure := { lower := (1288352963126080617573792577089545208512/1378113467118752178803179804914995610735), upper := (53760393447246707031413456170067907774506471/57505918755931290917099086899492936844750080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint437_valid : endpoint437.Valid 8 := by
  constructor
  · norm_num [endpoint437, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint437, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint437PositiveFacts : PositiveEndpointFacts 8
    endpoint437 :=
  { valid := endpoint437_valid
    positive := by
      norm_num [endpoint437] }

noncomputable def endpoint438 : EndpointCache :=
  { input := (639/256), certificate := { exponent := 1, mantissa := (639/512) }, enclosure := { lower := (1624671321190168370789046093066223084171004432322802845632/1776126981500521387900117016990329646678223624637410962355), upper := (118120105985659708635997466351133841459683555228840206724312283/129131536063013906985890107603264926632093570405638326607057920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint438_valid : endpoint438.Valid 8 := by
  constructor
  · norm_num [endpoint438, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint438, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint438PositiveFacts : PositiveEndpointFacts 8
    endpoint438 :=
  { valid := endpoint438_valid
    positive := by
      norm_num [endpoint438] }

noncomputable def endpoint439 : EndpointCache :=
  { input := (651/256), certificate := { exponent := 1, mantissa := (651/512) }, enclosure := { lower := (387352284495543483134785135836887580062631365543410072000/415020810230195804012801477093669352342653696643941507547), upper := (12296111148563543716388068709222965326373495058252000879047735/13174420599947335602582370088861439920765198946265279215571968) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint439_valid : endpoint439.Valid 8 := by
  constructor
  · norm_num [endpoint439, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint439, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint439PositiveFacts : PositiveEndpointFacts 8
    endpoint439 :=
  { valid := endpoint439_valid
    positive := by
      norm_num [endpoint439] }

noncomputable def endpoint440 : EndpointCache :=
  { input := (1285/512), certificate := { exponent := 1, mantissa := (1285/1024) }, enclosure := { lower := (11210122523957494794492171751009670268490797838772037650649664/12182408180163020958382606603801367802363533373234204699969429), upper := (29501455802431079798149725344029396486653031523385442829712696085901/32060199959571418995756338147091983618124063507672991824815546910720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint440_valid : endpoint440.Valid 8 := by
  constructor
  · norm_num [endpoint440, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint440, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint440PositiveFacts : PositiveEndpointFacts 8
    endpoint440 :=
  { valid := endpoint440_valid
    positive := by
      norm_num [endpoint440] }

noncomputable def endpoint441 : EndpointCache :=
  { input := (1307/512), certificate := { exponent := 1, mantissa := (1307/1024) }, enclosure := { lower := (131041089835148460093049994320665665134291944141022400/139827114318254694224862665015439551181274520977459479), upper := (50108915594576435987791475361881889489409802196078385228745/53468610095969685314383141500395371781537148026160139425792) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint441_valid : endpoint441.Valid 8 := by
  constructor
  · norm_num [endpoint441, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint441, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint441PositiveFacts : PositiveEndpointFacts 8
    endpoint441 :=
  { valid := endpoint441_valid
    positive := by
      norm_num [endpoint441] }

noncomputable def endpoint442 : EndpointCache :=
  { input := (325/128), certificate := { exponent := 1, mantissa := (325/256) }, enclosure := { lower := (1664326146693654605452187408354407988327930550582208/1786150702925569881903518045655461145672970627723203), upper := (3043339296573501563046367569954969675054238856133611537/3266104142492470641195004426341414666373432004979571200) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint442_valid : endpoint442.Valid 8 := by
  constructor
  · norm_num [endpoint442, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint442, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint442PositiveFacts : PositiveEndpointFacts 8
    endpoint442 :=
  { valid := endpoint442_valid
    positive := by
      norm_num [endpoint442] }

noncomputable def endpoint443 : EndpointCache :=
  { input := (661/256), certificate := { exponent := 1, mantissa := (661/512) }, enclosure := { lower := (385134840416839113669899591613214988728783851200/406013519529460084480846595100555172215732037791), upper := (260683913412002469343239184454851894009321195537912295/274815934882788470622043749746142176086629250027367424) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint443_valid : endpoint443.Valid 8 := by
  constructor
  · norm_num [endpoint443, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint443, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint443PositiveFacts : PositiveEndpointFacts 8
    endpoint443 :=
  { valid := endpoint443_valid
    positive := by
      norm_num [endpoint443] }

noncomputable def endpoint444 : EndpointCache :=
  { input := (167/64), certificate := { exponent := 1, mantissa := (167/128) }, enclosure := { lower := (2304321891770841462867055398024771907785573670336/2402560855999324581836954369600360592498779296875), upper := (98514371306570979217644455934677474218513703051769467/102714281715683124522693473209154616050507812500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint444_valid : endpoint444.Valid 8 := by
  constructor
  · norm_num [endpoint444, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint444, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint444PositiveFacts : PositiveEndpointFacts 8
    endpoint444 :=
  { valid := endpoint444_valid
    positive := by
      norm_num [endpoint444] }

noncomputable def endpoint445 : EndpointCache :=
  { input := (653/256), certificate := { exponent := 1, mantissa := (653/512) }, enclosure := { lower := (1993858325706871373386703625415414387943666633315532806464/2129281288997441024968778225959749363589809951324462890625), upper := (1333237259173672675465602830954806427853713390417943157015702313/1423790778076496885047922873908957526450325399772031250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint445_valid : endpoint445.Valid 8 := by
  constructor
  · norm_num [endpoint445, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint445, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint445PositiveFacts : PositiveEndpointFacts 8
    endpoint445 :=
  { valid := endpoint445_valid
    positive := by
      norm_num [endpoint445] }

noncomputable def endpoint446 : EndpointCache :=
  { input := (665/256), certificate := { exponent := 1, mantissa := (665/512) }, enclosure := { lower := (43097711121690898925297180064777953256172999354207834048/45146949433564275402554074708897370659126276835818359123), upper := (598935059205397290349445852098344562296867217878586084661267/627413605842447530165780055383076602531400601512629996497920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint446_valid : endpoint446.Valid 8 := by
  constructor
  · norm_num [endpoint446, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint446, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint446PositiveFacts : PositiveEndpointFacts 8
    endpoint446 :=
  { valid := endpoint446_valid
    positive := by
      norm_num [endpoint446] }

noncomputable def endpoint447 : EndpointCache :=
  { input := (85/32), certificate := { exponent := 1, mantissa := (85/64) }, enclosure := { lower := (16673436273488556061815588875500178619225664/17067431920039807020335183608725455363617029), upper := (181406989890884382750662595431059324042038871421/185693659290033100381246797662932954356153275520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint447_valid : endpoint447.Valid 8 := by
  constructor
  · norm_num [endpoint447, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint447, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint447PositiveFacts : PositiveEndpointFacts 8
    endpoint447 :=
  { valid := endpoint447_valid
    positive := by
      norm_num [endpoint447] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
