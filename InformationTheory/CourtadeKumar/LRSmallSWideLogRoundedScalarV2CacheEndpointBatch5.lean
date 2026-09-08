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

noncomputable def endpoint320 : EndpointCache :=
  { input := (513/256), certificate := { exponent := 1, mantissa := (513/512) }, enclosure := { lower := (216894443819543385737331348328751346836709281564186368064/312034157925769037849993509224841003306210041046142578125), upper := (4219898404726538174835434357695195869782631138558130456639799/6070936576603762400409473715478506560325622558593750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint320_valid : endpoint320.Valid 8 := by
  constructor
  · norm_num [endpoint320, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint320, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint320PositiveFacts : PositiveEndpointFacts 8
    endpoint320 :=
  { valid := endpoint320_valid
    positive := by
      norm_num [endpoint320] }

noncomputable def endpoint321 : EndpointCache :=
  { input := (515/256), certificate := { exponent := 1, mantissa := (515/512) }, enclosure := { lower := (493582824340056088661832797992339838449826283450828608/706137725952201587587023722171750483268791176909980633), upper := (260295844732075761981034919332534014634378786852986474098593/372388791158153029229892830124494334856629715055247386618880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint321_valid : endpoint321.Valid 8 := by
  constructor
  · norm_num [endpoint321, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint321, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint321PositiveFacts : PositiveEndpointFacts 8
    endpoint321 :=
  { valid := endpoint321_valid
    positive := by
      norm_num [endpoint321] }

noncomputable def endpoint322 : EndpointCache :=
  { input := (517/256), certificate := { exponent := 1, mantissa := (517/512) }, enclosure := { lower := (257209847109168467879837707394756916163080629824/365944655250483067333158968452529526537294667845), upper := (1768427975503701809240263654534051049472066422924081/2516026338270749866372896404811905864740988253434880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint322_valid : endpoint322.Valid 8 := by
  constructor
  · norm_num [endpoint322, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint322, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint322PositiveFacts : PositiveEndpointFacts 8
    endpoint322 :=
  { valid := endpoint322_valid
    positive := by
      norm_num [endpoint322] }

noncomputable def endpoint323 : EndpointCache :=
  { input := (519/256), certificate := { exponent := 1, mantissa := (519/512) }, enclosure := { lower := (240699658755038219885485208172742809460235452490615748032/340583917515558794203194813550459908610203681047492633355), upper := (42640426998987131181234451359722906858588604607794501455441929/60335122155716271510684367610091073730114802504925414984104960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint323_valid : endpoint323.Valid 8 := by
  constructor
  · norm_num [endpoint323, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint323, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint323PositiveFacts : PositiveEndpointFacts 8
    endpoint323 :=
  { valid := endpoint323_valid
    positive := by
      norm_num [endpoint323] }

noncomputable def endpoint324 : EndpointCache :=
  { input := (261/128), certificate := { exponent := 1, mantissa := (261/256) }, enclosure := { lower := (100459367304964504549735963960046991256728172103744/140997553970061770462193816750330393069083911346445), upper := (1491620722219568573997093232765317598567384633714024157/2093531681347477167822653791108905676289757915672015360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint324_valid : endpoint324.Valid 8 := by
  constructor
  · norm_num [endpoint324, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint324, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint324PositiveFacts : PositiveEndpointFacts 8
    endpoint324 :=
  { valid := endpoint324_valid
    positive := by
      norm_num [endpoint324] }

noncomputable def endpoint325 : EndpointCache :=
  { input := (523/256), certificate := { exponent := 1, mantissa := (523/512) }, enclosure := { lower := (17971092197088338458343019913594246399496624255552/25155362693743700165421207528802368137969970703125), upper := (9624454603056848351029226381733598039037419342705356269/13472004801359826110991658534465165861026093750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint325_valid : endpoint325.Valid 8 := by
  constructor
  · norm_num [endpoint325, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint325, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint325PositiveFacts : PositiveEndpointFacts 8
    endpoint325 :=
  { valid := endpoint325_valid
    positive := by
      norm_num [endpoint325] }

noncomputable def endpoint326 : EndpointCache :=
  { input := (529/256), certificate := { exponent := 1, mantissa := (529/512) }, enclosure := { lower := (218810634033456087865202199502669817698071593536/301470545559924158451246849942039995851970094165), upper := (118528848058645358537481814975362458222421298718967541/163305388647628676936406613626203297593028792128803840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint326_valid : endpoint326.Valid 8 := by
  constructor
  · norm_num [endpoint326, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint326, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint326PositiveFacts : PositiveEndpointFacts 8
    endpoint326 :=
  { valid := endpoint326_valid
    positive := by
      norm_num [endpoint326] }

noncomputable def endpoint327 : EndpointCache :=
  { input := (533/256), certificate := { exponent := 1, mantissa := (533/512) }, enclosure := { lower := (27797360493477843158893233525558636628918806622642073024/37904941339694209584636345446307487960211569061279296875), upper := (1167044410685042740647671824089173568463141742558597995638751/1591401057205721695201372327217773574521522515468750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint327_valid : endpoint327.Valid 8 := by
  constructor
  · norm_num [endpoint327, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint327, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint327PositiveFacts : PositiveEndpointFacts 8
    endpoint327 :=
  { valid := endpoint327_valid
    positive := by
      norm_num [endpoint327] }

noncomputable def endpoint328 : EndpointCache :=
  { input := (2049/1024), certificate := { exponent := 1, mantissa := (2049/2048) }, enclosure := { lower := (45972151071900860034315613142673727604635822405651941643257736000/66277117547123201617895322062333275152745436626596485390520032553), upper := (128610221960383607720851036085463799192730075893883325182672058016434275/185414743182070360903772180351277575902515745652594276440986346429231104) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint328_valid : endpoint328.Valid 8 := by
  constructor
  · norm_num [endpoint328, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint328, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint328PositiveFacts : PositiveEndpointFacts 8
    endpoint328 :=
  { valid := endpoint328_valid
    positive := by
      norm_num [endpoint328] }

noncomputable def endpoint329 : EndpointCache :=
  { input := (2085/1024), certificate := { exponent := 1, mantissa := (2085/2048) }, enclosure := { lower := (53734943260898025793744633844508624152007229715044358847884241472/75571010983994919950217493570874654711104674000363306507484154997), upper := (152968341427849960025925696485829117455673956819470372823419752774813839/215129508388358018520683143298080297059195897570314231900985293713059840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint329_valid : endpoint329.Valid 8 := by
  constructor
  · norm_num [endpoint329, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint329, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint329PositiveFacts : PositiveEndpointFacts 8
    endpoint329 :=
  { valid := endpoint329_valid
    positive := by
      norm_num [endpoint329] }

noncomputable def endpoint330 : EndpointCache :=
  { input := (521/256), certificate := { exponent := 1, mantissa := (521/512) }, enclosure := { lower := (49829603377923851874596736818690810610388096347287470400/70125985212556381324005898897092736719644759590177486497), upper := (26584293372371138213351982732576812146740173623970787197839345/37412493614839679661882443085194563410877357820398049756095488) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint330_valid : endpoint330.Valid 8 := by
  constructor
  · norm_num [endpoint330, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint330, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint330PositiveFacts : PositiveEndpointFacts 8
    endpoint330 :=
  { valid := endpoint330_valid
    positive := by
      norm_num [endpoint330] }

noncomputable def endpoint331 : EndpointCache :=
  { input := (2121/1024), certificate := { exponent := 1, mantissa := (2121/2048) }, enclosure := { lower := (28488092192430718507465541774118477511756949420739466582846737088/39122797260636501423928673970412310005380669946424943562345759695), upper := (1683630009946996454423902685265417661876366634170900481718311861872229/2312134962219468299010513815266241571426565947736601921709741628968960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint331_valid : endpoint331.Valid 8 := by
  constructor
  · norm_num [endpoint331, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint331, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint331PositiveFacts : PositiveEndpointFacts 8
    endpoint331 :=
  { valid := endpoint331_valid
    positive := by
      norm_num [endpoint331] }

noncomputable def endpoint332 : EndpointCache :=
  { input := (527/256), certificate := { exponent := 1, mantissa := (527/512) }, enclosure := { lower := (276139455961685464579796407307183068903982357672631477184/382452382472484657790854429414145315327626474441782359395), upper := (149018108726724261744683525903949244649997887402094571245127427/206389663296511400607519011124484691125922971679558966682792960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint332_valid : endpoint332.Valid 8 := by
  constructor
  · norm_num [endpoint332, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint332, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint332PositiveFacts : PositiveEndpointFacts 8
    endpoint332 :=
  { valid := endpoint332_valid
    positive := by
      norm_num [endpoint332] }

noncomputable def endpoint333 : EndpointCache :=
  { input := (537/256), certificate := { exponent := 1, mantissa := (537/512) }, enclosure := { lower := (327106790033840096687623098885198217069752049346023621184/441546534195039242717659930563873553270649239153876002645), upper := (59957367596145167246828143966521466172445485903291004585899479/80933713531813913033176194632635766820296922939948855780817920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint333_valid : endpoint333.Valid 8 := by
  constructor
  · norm_num [endpoint333, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint333, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint333PositiveFacts : PositiveEndpointFacts 8
    endpoint333 :=
  { valid := endpoint333_valid
    positive := by
      norm_num [endpoint333] }

noncomputable def endpoint334 : EndpointCache :=
  { input := (271/128), certificate := { exponent := 1, mantissa := (271/256) }, enclosure := { lower := (75906660924057431159330967516046383577126174974016/101196932444975527789103996042864131530128315098605), upper := (10532201261174996783561324460748586795888708740443926477/14041276770605244431793757658939483978068363976561640960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint334_valid : endpoint334.Valid 8 := by
  constructor
  · norm_num [endpoint334, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint334, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint334PositiveFacts : PositiveEndpointFacts 8
    endpoint334 :=
  { valid := endpoint334_valid
    positive := by
      norm_num [endpoint334] }

noncomputable def endpoint335 : EndpointCache :=
  { input := (539/256), certificate := { exponent := 1, mantissa := (539/512) }, enclosure := { lower := (338276508379042094367251697204181814086186292133264317632/454344105198439126348232447332859260155821720121858804855), upper := (2424766068802900940929115921046784884346351058224132086741211/3256738546062411657664130182481935176796930089833483913200640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint335_valid : endpoint335.Valid 8 := by
  constructor
  · norm_num [endpoint335, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint335, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint335PositiveFacts : PositiveEndpointFacts 8
    endpoint335 :=
  { valid := endpoint335_valid
    positive := by
      norm_num [endpoint335] }

noncomputable def endpoint336 : EndpointCache :=
  { input := (549/256), certificate := { exponent := 1, mantissa := (549/512) }, enclosure := { lower := (399534680431742366277853489524958406938991316901630874432/523690765514307058257512280886279395611546000107328748105), upper := (24956534848424099699597478768950073576358440070734791997478553/32711819977085676086997247113280556167479609350704182921630720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint336_valid : endpoint336.Valid 8 := by
  constructor
  · norm_num [endpoint336, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint336, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint336PositiveFacts : PositiveEndpointFacts 8
    endpoint336 :=
  { valid := endpoint336_valid
    positive := by
      norm_num [endpoint336] }

noncomputable def endpoint337 : EndpointCache :=
  { input := (139/64), certificate := { exponent := 1, mantissa := (139/128) }, enclosure := { lower := (5819114850408557965915677378834223304000/7502815253322265863485998016551995090129), upper := (207067387488515037259713869745310656571260425/266980177974219508486285753420986193287150336) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint337_valid : endpoint337.Valid 8 := by
  constructor
  · norm_num [endpoint337, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint337, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint337PositiveFacts : PositiveEndpointFacts 8
    endpoint337 :=
  { valid := endpoint337_valid
    positive := by
      norm_num [endpoint337] }

noncomputable def endpoint338 : EndpointCache :=
  { input := (2167/1024), certificate := { exponent := 1, mantissa := (2167/2048) }, enclosure := { lower := (2945044388521880645700741353372314327129847958507892695872/3928678693167926092691065507980360146638957179107666015625), upper := (2376391712863362488881438955324741836819829284280807058683819179/3170097981661517579305533051175448366644734215308125000000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint338_valid : endpoint338.Valid 8 := by
  constructor
  · norm_num [endpoint338, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint338, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint338PositiveFacts : PositiveEndpointFacts 8
    endpoint338 :=
  { valid := endpoint338_valid
    positive := by
      norm_num [endpoint338] }

noncomputable def endpoint339 : EndpointCache :=
  { input := (1103/512), certificate := { exponent := 1, mantissa := (1103/1024) }, enclosure := { lower := (950814772142760497376988071433520005241832545701391168/1238904085407049930369525365862352440822905263554127145), upper := (2147837373403327908712610259311203394991011858033362069900937/2798614950305742997908657108062565872082256907674014189434880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint339_valid : endpoint339.Valid 8 := by
  constructor
  · norm_num [endpoint339, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint339, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint339PositiveFacts : PositiveEndpointFacts 8
    endpoint339 :=
  { valid := endpoint339_valid
    positive := by
      norm_num [endpoint339] }

noncomputable def endpoint340 : EndpointCache :=
  { input := (279/128), certificate := { exponent := 1, mantissa := (279/256) }, enclosure := { lower := (14134795503062614115672979416890278027652231927910848/18140568271535719621431760707596753996796112060546875), upper := (224347479241143467880929342102751041276135499805819713491/287927099605814941831364905950975679437147890625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint340_valid : endpoint340.Valid 8 := by
  constructor
  · norm_num [endpoint340, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint340, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint340PositiveFacts : PositiveEndpointFacts 8
    endpoint340 :=
  { valid := endpoint340_valid
    positive := by
      norm_num [endpoint340] }

noncomputable def endpoint341 : EndpointCache :=
  { input := (551/256), certificate := { exponent := 1, mantissa := (551/512) }, enclosure := { lower := (82588158147843468608567650837757120276666002421433656000/107739044803302141339408574739497843695890357719221904047), upper := (46598222001930528269640436689941950899466249830495172602835135/60788954815098347395086463673818431361470041193770259589014528) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint341_valid : endpoint341.Valid 8 := by
  constructor
  · norm_num [endpoint341, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint341, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint341PositiveFacts : PositiveEndpointFacts 8
    endpoint341 :=
  { valid := endpoint341_valid
    positive := by
      norm_num [endpoint341] }

noncomputable def endpoint342 : EndpointCache :=
  { input := (561/256), certificate := { exponent := 1, mantissa := (561/512) }, enclosure := { lower := (97271808163496762596955081945456008190365579215060078400/123985238701244065662450517893346705660692121390187115897), upper := (1693307674114671543501461051964482786209199319317842245938105/2158335035311256695051938615487379452141328449160377313534976) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint342_valid : endpoint342.Valid 8 := by
  constructor
  · norm_num [endpoint342, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint342, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint342PositiveFacts : PositiveEndpointFacts 8
    endpoint342 :=
  { valid := endpoint342_valid
    positive := by
      norm_num [endpoint342] }

noncomputable def endpoint343 : EndpointCache :=
  { input := (8865/4096), certificate := { exponent := 1, mantissa := (8865/8192) }, enclosure := { lower := (100135362848557632926935907300536612129085210959535933253387667990037816128/129692211194330310664106855546702072994455134260076071633064418570697654153), upper := (1616008554603369118744348019894347920462588879727604017126401459131583563421441217/2093004030384789192771915820458009262482035625921330062271585522354375710158110720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint343_valid : endpoint343.Valid 8 := by
  constructor
  · norm_num [endpoint343, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint343, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint343PositiveFacts : PositiveEndpointFacts 8
    endpoint343 :=
  { valid := endpoint343_valid
    positive := by
      norm_num [endpoint343] }

noncomputable def endpoint344 : EndpointCache :=
  { input := (4509/2048), certificate := { exponent := 1, mantissa := (4509/4096) }, enclosure := { lower := (17856682941571134647875579384838104199347556821833126382729477122864448/22625973664035665416211991000410971450692195596914214978259429931640625), upper := (24429085631083110704349523641736783659694609907183162297461005274432295417467/30953780034715288571964641255986235246719767877096848600017508750000000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint344_valid : endpoint344.Valid 8 := by
  constructor
  · norm_num [endpoint344, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint344, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint344PositiveFacts : PositiveEndpointFacts 8
    endpoint344 :=
  { valid := endpoint344_valid
    positive := by
      norm_num [endpoint344] }

noncomputable def endpoint345 : EndpointCache :=
  { input := (277/128), certificate := { exponent := 1, mantissa := (277/256) }, enclosure := { lower := (1018401577037863222037871246004545011125467936400448/1319194829413154084493506064807126419068719963718845), upper := (144433788521534620364200732599684615502455305654644485397/187093487486691164879207004135205897258002140134461473280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint345_valid : endpoint345.Valid 8 := by
  constructor
  · norm_num [endpoint345, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint345, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint345PositiveFacts : PositiveEndpointFacts 8
    endpoint345 :=
  { valid := endpoint345_valid
    positive := by
      norm_num [endpoint345] }

noncomputable def endpoint346 : EndpointCache :=
  { input := (565/256), certificate := { exponent := 1, mantissa := (565/512) }, enclosure := { lower := (7233078147034344884271948237315895945690086298304/9136731902410666330778698256728132837899385037679), upper := (4184769784848369521211241042842015374898432801730554359/5286147609458715112335323663412628534695068207399562240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint346_valid : endpoint346.Valid 8 := by
  constructor
  · norm_num [endpoint346, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint346, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint346PositiveFacts : PositiveEndpointFacts 8
    endpoint346 :=
  { valid := endpoint346_valid
    positive := by
      norm_num [endpoint346] }

noncomputable def endpoint347 : EndpointCache :=
  { input := (143/64), certificate := { exponent := 1, mantissa := (143/128) }, enclosure := { lower := (540902261281158013700048855846143031076365358016/672796185398839514367634504076188876045888736355), upper := (138470981888829120322186282684862376393850199799181/172235823462102915678114433043504352267747516506880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint347_valid : endpoint347.Valid 8 := by
  constructor
  · norm_num [endpoint347, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint347, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint347PositiveFacts : PositiveEndpointFacts 8
    endpoint347 :=
  { valid := endpoint347_valid
    positive := by
      norm_num [endpoint347] }

noncomputable def endpoint348 : EndpointCache :=
  { input := (571/256), certificate := { exponent := 1, mantissa := (571/512) }, enclosure := { lower := (126453443012606097297193658690133758008104478400/157631000518009575773073803734857262251898922367), upper := (73937835549070312946411722234821513291886540909182695/92167476526882270992819345338985980667734307503674368) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint348_valid : endpoint348.Valid 8 := by
  constructor
  · norm_num [endpoint348, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint348, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint348PositiveFacts : PositiveEndpointFacts 8
    endpoint348 :=
  { valid := endpoint348_valid
    positive := by
      norm_num [endpoint348] }

noncomputable def endpoint349 : EndpointCache :=
  { input := (1127/512), certificate := { exponent := 1, mantissa := (1127/1024) }, enclosure := { lower := (231330515249752637136367163370377820400053049528232000/293198327090733892963551346045306573133456198803562253), upper := (76276149816644341330057079361545708108717110972554619036955/96675697994973505059085858228826845746148245519100974557184) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint349_valid : endpoint349.Valid 8 := by
  constructor
  · norm_num [endpoint349, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint349, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint349PositiveFacts : PositiveEndpointFacts 8
    endpoint349 :=
  { valid := endpoint349_valid
    positive := by
      norm_num [endpoint349] }

noncomputable def endpoint350 : EndpointCache :=
  { input := (2293/1024), certificate := { exponent := 1, mantissa := (2293/2048) }, enclosure := { lower := (1642181829718004690053936118318350097265727157484073370944/2037081290147499906715040501873485430382298787190896568945), upper := (15423582277330400930711630757027738475750728024889094192687932777/19132528223470458003855719918780014968285639143541661010292264960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint350_valid : endpoint350.Valid 8 := by
  constructor
  · norm_num [endpoint350, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint350, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint350PositiveFacts : PositiveEndpointFacts 8
    endpoint350 :=
  { valid := endpoint350_valid
    positive := by
      norm_num [endpoint350] }

noncomputable def endpoint351 : EndpointCache :=
  { input := (8239/4096), certificate := { exponent := 1, mantissa := (8239/8192) }, enclosure := { lower := (18025216164097026026903390675244756458693791875516523481626109805376/25792014914580706832139603729622284171657219656997771515697204704265), upper := (4514255848924857932687956696328144525560169923411833477746470614980335499/6459381691796066025563136231879438701988887413435272752987225885798645760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint351_valid : endpoint351.Valid 8 := by
  constructor
  · norm_num [endpoint351, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint351, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint351PositiveFacts : PositiveEndpointFacts 8
    endpoint351 :=
  { valid := endpoint351_valid
    positive := by
      norm_num [endpoint351] }

noncomputable def endpoint352 : EndpointCache :=
  { input := (4167/2048), certificate := { exponent := 1, mantissa := (4167/4096) }, enclosure := { lower := (672866443353678691018973396017782091379268944914369118969252677651648/947255414486603601842678187872275881548586335222857145290711796983095), upper := (2552112504128215925550165695029336634572813923745806334834659269101236530063/3592841272584580855014686728068003702022106916521433974944559611929993093120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint352_valid : endpoint352.Valid 8 := by
  constructor
  · norm_num [endpoint352, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint352, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint352PositiveFacts : PositiveEndpointFacts 8
    endpoint352 :=
  { valid := endpoint352_valid
    positive := by
      norm_num [endpoint352] }

noncomputable def endpoint353 : EndpointCache :=
  { input := (2097/1024), certificate := { exponent := 1, mantissa := (2097/2048) }, enclosure := { lower := (282881704530132671789116405679734296709758860731511356908207311936/394650066775068509576989828427119200697487413581729008331298828125), upper := (269973253151210257910813514665678959405015635878910603634577802737544853/376641394927988583347972628576332897331259667925167550223125000000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint353_valid : endpoint353.Valid 8 := by
  constructor
  · norm_num [endpoint353, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint353, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint353PositiveFacts : PositiveEndpointFacts 8
    endpoint353 :=
  { valid := endpoint353_valid
    positive := by
      norm_num [endpoint353] }

noncomputable def endpoint354 : EndpointCache :=
  { input := (1061/512), certificate := { exponent := 1, mantissa := (1061/1024) }, enclosure := { lower := (74368363234080107012020113979180173079647252239674304/102064266017793457518982517838881274759053192138671875), upper := (161597102649531005511497393531089475706833805847875257815307/221778301429511902059807644522604610599639934687500000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint354_valid : endpoint354.Valid 8 := by
  constructor
  · norm_num [endpoint354, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint354, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint354PositiveFacts : PositiveEndpointFacts 8
    endpoint354 :=
  { valid := endpoint354_valid
    positive := by
      norm_num [endpoint354] }

noncomputable def endpoint355 : EndpointCache :=
  { input := (267/128), certificate := { exponent := 1, mantissa := (267/256) }, enclosure := { lower := (9490429205975649869900253559908218399940652218130624/12908313081229696138146042607426889318578739925345735), upper := (432459888306170467816863281250693505769031194263784435077/588206010485474793623038869535228492468996020918154452480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint355_valid : endpoint355.Valid 8 := by
  constructor
  · norm_num [endpoint355, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint355, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint355PositiveFacts : PositiveEndpointFacts 8
    endpoint355 :=
  { valid := endpoint355_valid
    positive := by
      norm_num [endpoint355] }

noncomputable def endpoint356 : EndpointCache :=
  { input := (531/256), certificate := { exponent := 1, mantissa := (531/512) }, enclosure := { lower := (767756846830807084061543965245352501331201978550968000/1052320556586409634521153714278035929556284549418540511), upper := (6626399823689661378713375897999251032387842841187547002825/9082428392389217782747146114545974102867498191095791930368) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint356_valid : endpoint356.Valid 8 := by
  constructor
  · norm_num [endpoint356, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint356, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint356PositiveFacts : PositiveEndpointFacts 8
    endpoint356 :=
  { valid := endpoint356_valid
    positive := by
      norm_num [endpoint356] }

noncomputable def endpoint357 : EndpointCache :=
  { input := (269/128), certificate := { exponent := 1, mantissa := (269/256) }, enclosure := { lower := (101069293101901894982400953806079296563762752/136087064966961144037214107811450958251953125), upper := (1988581703842386540085371842481428705400090881963/2677571326252803492279632091522216796875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint357_valid : endpoint357.Valid 8 := by
  constructor
  · norm_num [endpoint357, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint357, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint357PositiveFacts : PositiveEndpointFacts 8
    endpoint357 :=
  { valid := endpoint357_valid
    positive := by
      norm_num [endpoint357] }

noncomputable def endpoint358 : EndpointCache :=
  { input := (541/256), certificate := { exponent := 1, mantissa := (541/512) }, enclosure := { lower := (375041678013501901589303686207849221498751115200/501230566502497675340460688610540049245933349267), upper := (207767093790521478684040926288772902173751415512376555/277673714153319672175809774119221418641459140560329728) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint358_valid : endpoint358.Valid 8 := by
  constructor
  · norm_num [endpoint358, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint358, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint358PositiveFacts : PositiveEndpointFacts 8
    endpoint358 :=
  { valid := endpoint358_valid
    positive := by
      norm_num [endpoint358] }

noncomputable def endpoint359 : EndpointCache :=
  { input := (8581/4096), certificate := { exponent := 1, mantissa := (8581/8192) }, enclosure := { lower := (399700415634011614286563963228406809642702314053617790490917835200/540471981335414043107255137680789898103271238938895812032819521467), upper := (56194324027135503816197577034650363541502164098038193306488077886819788355/75985552537013254617552590216214251366386409493867150754670580755797229568) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint359_valid : endpoint359.Valid 8 := by
  constructor
  · norm_num [endpoint359, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint359, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint359PositiveFacts : PositiveEndpointFacts 8
    endpoint359 :=
  { valid := endpoint359_valid
    positive := by
      norm_num [endpoint359] }

noncomputable def endpoint360 : EndpointCache :=
  { input := (273/128), certificate := { exponent := 1, mantissa := (273/256) }, enclosure := { lower := (2320375905582598451558435857929429566790923601876800/3063438975686469372873493952020600656462452063064729), upper := (91387114691216967148911139584365523239861547381514765/120652365811651716839325300264195964316059650483780096) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint360_valid : endpoint360.Valid 8 := by
  constructor
  · norm_num [endpoint360, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint360, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint360PositiveFacts : PositiveEndpointFacts 8
    endpoint360 :=
  { valid := endpoint360_valid
    positive := by
      norm_num [endpoint360] }

noncomputable def endpoint361 : EndpointCache :=
  { input := (257/128), certificate := { exponent := 1, mantissa := (257/256) }, enclosure := { lower := (469404382929808380277102844339528738266839232/673419694209083339848701021624750401748978855), upper := (61766107867303620761555672109144135496890399003943/88611257042808022190651475229471156863737633656320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint361_valid : endpoint361.Valid 8 := by
  constructor
  · norm_num [endpoint361, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint361, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint361PositiveFacts : PositiveEndpointFacts 8
    endpoint361 :=
  { valid := endpoint361_valid
    positive := by
      norm_num [endpoint361] }

noncomputable def endpoint362 : EndpointCache :=
  { input := (511/256), certificate := { exponent := 0, mantissa := (511/256) }, enclosure := { lower := (995451208660467998284515639124640842248574080/1440194620571897941891068306069753530407749811), upper := (37205985271446206882677214292978232065469863017205/53828714138495257476120569007663107952520056935936) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint362_valid : endpoint362.Valid 8 := by
  constructor
  · norm_num [endpoint362, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint362, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint362PositiveFacts : PositiveEndpointFacts 8
    endpoint362 :=
  { valid := endpoint362_valid
    positive := by
      norm_num [endpoint362] }

noncomputable def endpoint363 : EndpointCache :=
  { input := (545/256), certificate := { exponent := 1, mantissa := (545/512) }, enclosure := { lower := (10683109273439098962448387233271103328462254358781317824/14138421425790263596722165359105333445855707787144384879), upper := (851718537256322756833793561005373800764281974026718454547097/1127195747043575758294100863372786355637593343121362616181760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint363_valid : endpoint363.Valid 8 := by
  constructor
  · norm_num [endpoint363, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint363, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint363PositiveFacts : PositiveEndpointFacts 8
    endpoint363 :=
  { valid := endpoint363_valid
    positive := by
      norm_num [endpoint363] }

noncomputable def endpoint364 : EndpointCache :=
  { input := (543/256), certificate := { exponent := 1, mantissa := (543/512) }, enclosure := { lower := (51666793171320103854694057932244503138575721580687487552/68712066780804405818722973505058869791902473907470703125), upper := (9576130335432599275448777139129098360196856782181541979055943/12735369305421411792065390801321631162710372123906250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint364_valid : endpoint364.Valid 8 := by
  constructor
  · norm_num [endpoint364, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint364, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint364PositiveFacts : PositiveEndpointFacts 8
    endpoint364 :=
  { valid := endpoint364_valid
    positive := by
      norm_num [endpoint364] }

noncomputable def endpoint365 : EndpointCache :=
  { input := (275/128), certificate := { exponent := 1, mantissa := (275/256) }, enclosure := { lower := (24682513773103396784267059551396943431460544/32275658257741251016497886857638895670516479), upper := (28721471226693732398406305018650696206119684111/37557129609008001182833904707070714962055539200) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint365_valid : endpoint365.Valid 8 := by
  constructor
  · norm_num [endpoint365, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint365, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint365PositiveFacts : PositiveEndpointFacts 8
    endpoint365 :=
  { valid := endpoint365_valid
    positive := by
      norm_num [endpoint365] }

noncomputable def endpoint366 : EndpointCache :=
  { input := (547/256), certificate := { exponent := 1, mantissa := (547/512) }, enclosure := { lower := (26937777091108735724323973060711978510308829134912/35478458189180538324998294169005646739969719253485), upper := (15088603552725340959024708973374346802308371858957107221/19872477828589316570904644516296794897165758906016046080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint366_valid : endpoint366.Valid 8 := by
  constructor
  · norm_num [endpoint366, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint366, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint366PositiveFacts : PositiveEndpointFacts 8
    endpoint366 :=
  { valid := endpoint366_valid
    positive := by
      norm_num [endpoint366] }

noncomputable def endpoint367 : EndpointCache :=
  { input := (557/256), certificate := { exponent := 1, mantissa := (557/512) }, enclosure := { lower := (65095267056066992493419530334784081214139719727866885312/83735900565936426392033096186247304820440346354499867735), upper := (37128258112358793636017957018492542528658763340419334473986351/47760278133992027648371133005557502755824919469523380560276480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint367_valid : endpoint367.Valid 8 := by
  constructor
  · norm_num [endpoint367, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint367, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint367PositiveFacts : PositiveEndpointFacts 8
    endpoint367 :=
  { valid := endpoint367_valid
    positive := by
      norm_num [endpoint367] }

noncomputable def endpoint368 : EndpointCache :=
  { input := (2183/1024), certificate := { exponent := 1, mantissa := (2183/2048) }, enclosure := { lower := (406514442083866134779506495321063955341923472938413956969024263616/537018858754247399258009897653418605671514493124965716746414473355), upper := (3634876610536212242999530289110644815382237401978294281804822892934943643/4801790642833498409288645044541082895077032503262413453956803769687920640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint368_valid : endpoint368.Valid 8 := by
  constructor
  · norm_num [endpoint368, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint368, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint368PositiveFacts : PositiveEndpointFacts 8
    endpoint368 :=
  { valid := endpoint368_valid
    positive := by
      norm_num [endpoint368] }

noncomputable def endpoint369 : EndpointCache :=
  { input := (2209/1024), certificate := { exponent := 1, mantissa := (2209/2048) }, enclosure := { lower := (573513956558592744059140315886243090058292718022557844800/745963193808865690344377156960840562963245455694609560689), upper := (5189191101431827716191735007504147466021067395611984652675858865/6749522719227020533640106556319730907487474530833991760125956096) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint369_valid : endpoint369.Valid 8 := by
  constructor
  · norm_num [endpoint369, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint369, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint369PositiveFacts : PositiveEndpointFacts 8
    endpoint369 :=
  { valid := endpoint369_valid
    positive := by
      norm_num [endpoint369] }

noncomputable def endpoint370 : EndpointCache :=
  { input := (1117/512), certificate := { exponent := 1, mantissa := (1117/1024) }, enclosure := { lower := (278207636548987140261349260140848238893068190603630948779200/356641171119836815458103191395895575952792524231862111522711), upper := (636432254906285321742371660645706883555722927620612989159003254415/815858049312476616431004190288313053878823423113195476113138046976) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint370_valid : endpoint370.Valid 8 := by
  constructor
  · norm_num [endpoint370, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint370, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint370PositiveFacts : PositiveEndpointFacts 8
    endpoint370 :=
  { valid := endpoint370_valid
    positive := by
      norm_num [endpoint370] }

noncomputable def endpoint371 : EndpointCache :=
  { input := (555/256), certificate := { exponent := 1, mantissa := (555/512) }, enclosure := { lower := (616776608860777125847472507902974130448282953447363136/797084578767996482565007372615014891417028384820208021), upper := (116842163413442843626408884559673980903521290750253219277327/150999702601809253657114996668188421030041857220340207498240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint371_valid : endpoint371.Valid 8 := by
  constructor
  · norm_num [endpoint371, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint371, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint371PositiveFacts : PositiveEndpointFacts 8
    endpoint371 :=
  { valid := endpoint371_valid
    positive := by
      norm_num [endpoint371] }

noncomputable def endpoint372 : EndpointCache :=
  { input := (563/256), certificate := { exponent := 1, mantissa := (563/512) }, enclosure := { lower := (502404651197345510417560648175933671264150026537900816064/637486689237441924812944116241691387258470058441162109375), upper := (289642316674337037614354980064884678263920276770381864408041623/367518726185656118957760038342729985051155090332031250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint372_valid : endpoint372.Valid 8 := by
  constructor
  · norm_num [endpoint372, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint372, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint372PositiveFacts : PositiveEndpointFacts 8
    endpoint372 :=
  { valid := endpoint372_valid
    positive := by
      norm_num [endpoint372] }

noncomputable def endpoint373 : EndpointCache :=
  { input := (559/256), certificate := { exponent := 1, mantissa := (559/512) }, enclosure := { lower := (4687106675404279033349355165795803099660433445568/6001631952715509422483071924133312397528645206895), upper := (29483240819378839303668140830710976009902015698415773/37751979734567044412967803280491144498283043678571520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint373_valid : endpoint373.Valid 8 := by
  constructor
  · norm_num [endpoint373, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint373, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint373PositiveFacts : PositiveEndpointFacts 8
    endpoint373 :=
  { valid := endpoint373_valid
    positive := by
      norm_num [endpoint373] }

noncomputable def endpoint374 : EndpointCache :=
  { input := (283/128), certificate := { exponent := 1, mantissa := (283/256) }, enclosure := { lower := (41803842819752955854342203248661713418794793131200/52688387281303204951358206970212420625613630759927), upper := (865315677460490663358535465426747324948333028180673385/1090619509073101312090285536736556985566987520370054656) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint374_valid : endpoint374.Valid 8 := by
  constructor
  · norm_num [endpoint374, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint374, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint374PositiveFacts : PositiveEndpointFacts 8
    endpoint374 :=
  { valid := endpoint374_valid
    positive := by
      norm_num [endpoint374] }

noncomputable def endpoint375 : EndpointCache :=
  { input := (2233/1024), certificate := { exponent := 1, mantissa := (2233/2048) }, enclosure := { lower := (2677001626363464118182639305800716066825566910387237808576/3433684608432340105020389795499237821704612589805226912155), upper := (317984968292192233753467695663530971578835040418155207860115799/407866792528027087034741981468581465413360701867424073533419520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint375_valid : endpoint375.Valid 8 := by
  constructor
  · norm_num [endpoint375, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint375, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint375PositiveFacts : PositiveEndpointFacts 8
    endpoint375 :=
  { valid := endpoint375_valid
    positive := by
      norm_num [endpoint375] }

noncomputable def endpoint376 : EndpointCache :=
  { input := (2259/1024), certificate := { exponent := 1, mantissa := (2259/2048) }, enclosure := { lower := (8537747171361130712081673864660429121219355067404338212535787200/10790805810673277085642624365306522329320685679695638531278840031), upper := (8777623909177403029106512421142593530234071657307989241030758700694015/11093984290729953478640839539474174380685279664552367191453650320510976) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint376_valid : endpoint376.Valid 8 := by
  constructor
  · norm_num [endpoint376, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint376, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint376PositiveFacts : PositiveEndpointFacts 8
    endpoint376 :=
  { valid := endpoint376_valid
    positive := by
      norm_num [endpoint376] }

noncomputable def endpoint377 : EndpointCache :=
  { input := (281/128), certificate := { exponent := 1, mantissa := (281/256) }, enclosure := { lower := (116815068302205619356784160883904630901469376/148558365539958591621395239178036107678331655), upper := (16806417879161986854009296600303549789845607970967/21373389166964922493753375851022410883896931868160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint377_valid : endpoint377.Valid 8 := by
  constructor
  · norm_num [endpoint377, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint377, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint377PositiveFacts : PositiveEndpointFacts 8
    endpoint377 :=
  { valid := endpoint377_valid
    positive := by
      norm_num [endpoint377] }

noncomputable def endpoint378 : EndpointCache :=
  { input := (569/256), certificate := { exponent := 1, mantissa := (569/512) }, enclosure := { lower := (553496496360862133380948353338490258212690856848061332032/692994147056785751392958019251869120154740258202750599605), upper := (322498061618616276175167437431098117682890710552258322185094437/403777197747518558763615347665217054072880339883381853363450880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint378_valid : endpoint378.Valid 8 := by
  constructor
  · norm_num [endpoint378, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint378, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint378PositiveFacts : PositiveEndpointFacts 8
    endpoint378 :=
  { valid := endpoint378_valid
    positive := by
      norm_num [endpoint378] }

noncomputable def endpoint379 : EndpointCache :=
  { input := (285/128), certificate := { exponent := 1, mantissa := (285/256) }, enclosure := { lower := (3432987132854636327311001157033508887594785113203776/4288773686039722623440865045883897539396399836005821), upper := (166980497776576379260865296863462869976050126180504868983/208605952088972108404163675831792776316240888023323133440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint379_valid : endpoint379.Valid 8 := by
  constructor
  · norm_num [endpoint379, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint379, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint379PositiveFacts : PositiveEndpointFacts 8
    endpoint379 :=
  { valid := endpoint379_valid
    positive := by
      norm_num [endpoint379] }

noncomputable def endpoint380 : EndpointCache :=
  { input := (575/256), certificate := { exponent := 1, mantissa := (575/512) }, enclosure := { lower := (11078386921082168569385965893435190762737917875946571328/13690667691900560013966507399753719410995994746751943973), upper := (6522954359580553203895523922365155181347776718069741053640613/8061065136991049736223479556974989989194441706887544611302400) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint380_valid : endpoint380.Valid 8 := by
  constructor
  · norm_num [endpoint380, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint380, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint380PositiveFacts : PositiveEndpointFacts 8
    endpoint380 :=
  { valid := endpoint380_valid
    positive := by
      norm_num [endpoint380] }

noncomputable def endpoint381 : EndpointCache :=
  { input := (9135/4096), certificate := { exponent := 1, mantissa := (9135/8192) }, enclosure := { lower := (131660210822580893876643312806423178133791429008509753859215717657915857088/164143913619411857978863124948853350840145219571774234440821240784123848103), upper := (312782536441119930018892168790681844247966564134016473666230564494824139719334201/389953412707364362763225548678491928523916195232272613276370205306027343461335040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint381_valid : endpoint381.Valid 8 := by
  constructor
  · norm_num [endpoint381, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint381, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint381PositiveFacts : PositiveEndpointFacts 8
    endpoint381 :=
  { valid := endpoint381_valid
    positive := by
      norm_num [endpoint381] }

noncomputable def endpoint382 : EndpointCache :=
  { input := (9239/4096), certificate := { exponent := 1, mantissa := (9239/8192) }, enclosure := { lower := (730289445181340398691344959113158804843159221480521411586837694775521604032/897798138631738185804866233277104740277019350193491059519623645135039063355), upper := (110545212678952931773747466187608970399001446913087592968440647664135029578409723627/135901298734180419152300591173585644673751151025154685319607138015684622849422868480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint382_valid : endpoint382.Valid 8 := by
  constructor
  · norm_num [endpoint382, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint382, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint382PositiveFacts : PositiveEndpointFacts 8
    endpoint382 :=
  { valid := endpoint382_valid
    positive := by
      norm_num [endpoint382] }

noncomputable def endpoint383 : EndpointCache :=
  { input := (1149/512), certificate := { exponent := 1, mantissa := (1149/1024) }, enclosure := { lower := (217662397799973793360894478221171037965563401377455188458432/269276627737620903015251730507052123811910253659605157056835), upper := (170730905915941043920213807933480845854822973410325394472881096393/211216278371346034390715213382043573084081412406535731512868464640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint383_valid : endpoint383.Valid 8 := by
  constructor
  · norm_num [endpoint383, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint383, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint383PositiveFacts : PositiveEndpointFacts 8
    endpoint383 :=
  { valid := endpoint383_valid
    positive := by
      norm_num [endpoint383] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
