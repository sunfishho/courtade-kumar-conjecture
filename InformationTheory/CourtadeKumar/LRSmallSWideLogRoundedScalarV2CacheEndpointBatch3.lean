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

noncomputable def endpoint192 : EndpointCache :=
  { input := (815742035/536870912), certificate := { exponent := 0, mantissa := (815742035/536870912) }, enclosure := { lower := (27761251938211077199476123979506209136968876766451341025243490998403849951794494910331394673117125937247117637400123643576314964253688108416/66360422655882271302036957623104443457976472291350706628725413891158248543473939879731653743030323493963907150883775887745073776261913792745), upper := (694742256648830229666589231332640745763276651584724209433635523902461613161014532920613861765840665262020130038173873192194792504996280873866760936618179131/1660710038950169113382228363369784130301801759635411618834470009825482316899007936375126929612525986400177498473777294551383798755701732807661937153152122880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint192_valid : endpoint192.Valid 8 := by
  constructor
  · norm_num [endpoint192, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint192, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint192PositiveFacts : PositiveEndpointFacts 8
    endpoint192 :=
  { valid := endpoint192_valid
    positive := by
      norm_num [endpoint192] }

noncomputable def endpoint193 : EndpointCache :=
  { input := (12599/8192), certificate := { exponent := 0, mantissa := (12599/8192) }, enclosure := { lower := (9716807051827990492145308090146563678065783257998011069953651249792/22573110405493684735714365034712099083228204792023806986409370880135), upper := (2005762900755697581415921254669514990561577094071409399934834523658731693367/4659586957292583878414586430625181472351717821230414958129506938369161052160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint193_valid : endpoint193.Valid 8 := by
  constructor
  · norm_num [endpoint193, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint193, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint193PositiveFacts : PositiveEndpointFacts 8
    endpoint193 :=
  { valid := endpoint193_valid
    positive := by
      norm_num [endpoint193] }

noncomputable def endpoint194 : EndpointCache :=
  { input := (377/256), certificate := { exponent := 0, mantissa := (377/256) }, enclosure := { lower := (554594146787379363387548376246790252092150656/1432809002719435580825036433699671210671583805), upper := (8234613891525833840933288708915198704868989986593/21274348072378179504090140967572718136051676336640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint194_valid : endpoint194.Valid 8 := by
  constructor
  · norm_num [endpoint194, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint194, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint194PositiveFacts : PositiveEndpointFacts 8
    endpoint194 :=
  { valid := endpoint194_valid
    positive := by
      norm_num [endpoint194] }

noncomputable def endpoint195 : EndpointCache :=
  { input := (375/256), certificate := { exponent := 0, mantissa := (375/256) }, enclosure := { lower := (2459044408675368623128914655611188269065947008/6441528607840281498721628307295816447762949685), upper := (31475768431127275705467612067510483131677537783531/82451566180355603183636842333386450531365755968000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint195_valid : endpoint195.Valid 8 := by
  constructor
  · norm_num [endpoint195, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint195, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint195PositiveFacts : PositiveEndpointFacts 8
    endpoint195 :=
  { valid := endpoint195_valid
    positive := by
      norm_num [endpoint195] }

noncomputable def endpoint196 : EndpointCache :=
  { input := (381/256), certificate := { exponent := 0, mantissa := (381/256) }, enclosure := { lower := (45414758522503575681475769420413817114384000/114215929812028359353630476411928546398059807), upper := (421864179740275349862476071018082854580643434875/1060968088585333148372924014029891685855348698624) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint196_valid : endpoint196.Valid 8 := by
  constructor
  · norm_num [endpoint196, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint196, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint196PositiveFacts : PositiveEndpointFacts 8
    endpoint196 :=
  { valid := endpoint196_valid
    positive := by
      norm_num [endpoint196] }

noncomputable def endpoint197 : EndpointCache :=
  { input := (195/128), certificate := { exponent := 0, mantissa := (195/128) }, enclosure := { lower := (824014484770808965546473015222469846577792/1957421824477676053965582650088941512939815), upper := (210947708103879112548567482837044007814903989/501099987066285069815189158422769027312592640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint197_valid : endpoint197.Valid 8 := by
  constructor
  · norm_num [endpoint197, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint197, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint197PositiveFacts : PositiveEndpointFacts 8
    endpoint197 :=
  { valid := endpoint197_valid
    positive := by
      norm_num [endpoint197] }

noncomputable def endpoint198 : EndpointCache :=
  { input := (197/128), certificate := { exponent := 0, mantissa := (197/128) }, enclosure := { lower := (7913400934696041760441853255661908802432/18353172401362044219858944416046142578125), upper := (399088635945603639726111422104686022128544389/925587190545490614095926284790039062500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint198_valid : endpoint198.Valid 8 := by
  constructor
  · norm_num [endpoint198, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint198, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint198PositiveFacts : PositiveEndpointFacts 8
    endpoint198 :=
  { valid := endpoint198_valid
    positive := by
      norm_num [endpoint198] }

noncomputable def endpoint199 : EndpointCache :=
  { input := (213/128), certificate := { exponent := 0, mantissa := (213/128) }, enclosure := { lower := (40882813355913145792089100850084677489280/80278562391539038946415452187613842679719), upper := (743086015729376983527797886684562712547106405/1459143150028613571890047258962069204546572544) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint199_valid : endpoint199.Valid 8 := by
  constructor
  · norm_num [endpoint199, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint199, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint199PositiveFacts : PositiveEndpointFacts 8
    endpoint199 :=
  { valid := endpoint199_valid
    positive := by
      norm_num [endpoint199] }

noncomputable def endpoint200 : EndpointCache :=
  { input := (427/256), certificate := { exponent := 0, mantissa := (427/256) }, enclosure := { lower := (8407187803300571492680011415825971205468947072/16432916066694285873928277439765628769974978535), upper := (262573289538032595158777556937481680962333878855769/513232834594995936414527960998760117743858529605120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint200_valid : endpoint200.Valid 8 := by
  constructor
  · norm_num [endpoint200, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint200, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint200PositiveFacts : PositiveEndpointFacts 8
    endpoint200 :=
  { valid := endpoint200_valid
    positive := by
      norm_num [endpoint200] }

noncomputable def endpoint201 : EndpointCache :=
  { input := (1703/1024), certificate := { exponent := 0, mantissa := (1703/1024) }, enclosure := { lower := (3742352159911837364079826458149198173776059049974864512/7357061147351560846647050713629595029105422461789191735), upper := (1004028176507129098803481146175172541751915912922203170246691/1973811221100655556425243941858256791168635581428498672199680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint201_valid : endpoint201.Valid 8 := by
  constructor
  · norm_num [endpoint201, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint201, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint201PositiveFacts : PositiveEndpointFacts 8
    endpoint201 :=
  { valid := endpoint201_valid
    positive := by
      norm_num [endpoint201] }

noncomputable def endpoint202 : EndpointCache :=
  { input := (1723/1024), certificate := { exponent := 0, mantissa := (1723/1024) }, enclosure := { lower := (9967354201064463968766939807008002148320605407549401728/19155080132186093212380259421475855121038572339538264215), upper := (35171842650076581702262327144636882441819314402926846801555007/67592607882765595862899070941599535869029294368818031088527360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint202_valid : endpoint202.Valid 8 := by
  constructor
  · norm_num [endpoint202, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint202, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint202PositiveFacts : PositiveEndpointFacts 8
    endpoint202 :=
  { valid := endpoint202_valid
    positive := by
      norm_num [endpoint202] }

noncomputable def endpoint203 : EndpointCache :=
  { input := (3381/2048), certificate := { exponent := 0, mantissa := (3381/2048) }, enclosure := { lower := (2368910715397715686147819274721667502547564515451530935089536/4725461357720054822091626962176119433759125218094873784792705), upper := (1562192385017460876602065088540295312356277681795103960039419340501/3116233845116636472757255949968815017309057679823973086624258068480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint203_valid : endpoint203.Valid 8 := by
  constructor
  · norm_num [endpoint203, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint203, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint203PositiveFacts : PositiveEndpointFacts 8
    endpoint203 :=
  { valid := endpoint203_valid
    positive := by
      norm_num [endpoint203] }

noncomputable def endpoint204 : EndpointCache :=
  { input := (3419/2048), certificate := { exponent := 0, mantissa := (3419/2048) }, enclosure := { lower := (3879985637597164889205057695956164142556950393150534263936/7570934083669602457595490573114896922192264060367045187795), upper := (597100967028336849242415703654548356329697977086658193667162369/1165110514252130272605689575558125211376824582071754099208826880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint204_valid : endpoint204.Valid 8 := by
  constructor
  · norm_num [endpoint204, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint204, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint204PositiveFacts : PositiveEndpointFacts 8
    endpoint204 :=
  { valid := endpoint204_valid
    positive := by
      norm_num [endpoint204] }

noncomputable def endpoint205 : EndpointCache :=
  { input := (433/256), certificate := { exponent := 0, mantissa := (433/256) }, enclosure := { lower := (757480742774364719086473503383291241591083392/1441282316299642985666857409262662669320966865), upper := (167930450813347657135916108148753271167895576272177/319526524394365651350399620203895263137781070103040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint205_valid : endpoint205.Valid 8 := by
  constructor
  · norm_num [endpoint205, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint205, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint205PositiveFacts : PositiveEndpointFacts 8
    endpoint205 :=
  { valid := endpoint205_valid
    positive := by
      norm_num [endpoint205] }

noncomputable def endpoint206 : EndpointCache :=
  { input := (1729/1024), certificate := { exponent := 0, mantissa := (1729/1024) }, enclosure := { lower := (2073551675325582228940531218141182249049195292326983040/3958469001687839373316778353137819312024553781161039657), upper := (80686042819149752946982064202927164375901386787018530849355/154031945793677205694502479277298825069499436732538375133184) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint206_valid : endpoint206.Valid 8 := by
  constructor
  · norm_num [endpoint206, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint206, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint206PositiveFacts : PositiveEndpointFacts 8
    endpoint206 :=
  { valid := endpoint206_valid
    positive := by
      norm_num [endpoint206] }

noncomputable def endpoint207 : EndpointCache :=
  { input := (1749/1024), certificate := { exponent := 0, mantissa := (1749/1024) }, enclosure := { lower := (21259072933345630600991437414126586486018303718596451200/39712262504631492279113620332698904330792034613682327213), upper := (2307544813630279081371778372067542363450308770477603951005925/4310527821302720697944108805392469871681490605107534525007872) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint207_valid : endpoint207.Valid 8 := by
  constructor
  · norm_num [endpoint207, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint207, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint207PositiveFacts : PositiveEndpointFacts 8
    endpoint207 :=
  { valid := endpoint207_valid
    positive := by
      norm_num [endpoint207] }

noncomputable def endpoint208 : EndpointCache :=
  { input := (1745/1024), certificate := { exponent := 0, mantissa := (1745/1024) }, enclosure := { lower := (379390520018995882765233006560520859640980408496633728/711751318596767231476038604505844355896327026698088085), upper := (271170133091503267296727962126155305422823446209438509658609/508725678469676572231961544647761265065611534986511854929920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint208_valid : endpoint208.Valid 8 := by
  constructor
  · norm_num [endpoint208, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint208, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint208PositiveFacts : PositiveEndpointFacts 8
    endpoint208 :=
  { valid := endpoint208_valid
    positive := by
      norm_num [endpoint208] }

noncomputable def endpoint209 : EndpointCache :=
  { input := (1765/1024), certificate := { exponent := 0, mantissa := (1765/1024) }, enclosure := { lower := (1007241968846446806589890919731023651283075909004712832/1850071204043362926414859106539879084482295709689944365), upper := (145635907679427447125602469611580402539932532434114769938669/267499575307184993494812780383673268970393757909217427802112) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint209_valid : endpoint209.Valid 8 := by
  constructor
  · norm_num [endpoint209, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint209, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint209PositiveFacts : PositiveEndpointFacts 8
    endpoint209 :=
  { valid := endpoint209_valid
    positive := by
      norm_num [endpoint209] }

noncomputable def endpoint210 : EndpointCache :=
  { input := (879/512), certificate := { exponent := 0, mantissa := (879/512) }, enclosure := { lower := (264468507782438064584749948865767370594040317760128/489339404165155239478468328769091657700433416206215), upper := (79349015372890223110327842638629075211892027066331800781/146817480110479856811203809617248108243176438731183098880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint210_valid : endpoint210.Valid 8 := by
  constructor
  · norm_num [endpoint210, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint210, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint210PositiveFacts : PositiveEndpointFacts 8
    endpoint210 :=
  { valid := endpoint210_valid
    positive := by
      norm_num [endpoint210] }

noncomputable def endpoint211 : EndpointCache :=
  { input := (119/64), certificate := { exponent := 0, mantissa := (119/64) }, enclosure := { lower := (1463824631750566542456803553147925120/2360092327326096907742922304736939511), upper := (3185282413728626497155396216372785451745/5135560904261586871248598935107580375936) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint211_valid : endpoint211.Valid 8 := by
  constructor
  · norm_num [endpoint211, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint211, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint211PositiveFacts : PositiveEndpointFacts 8
    endpoint211 :=
  { valid := endpoint211_valid
    positive := by
      norm_num [endpoint211] }

noncomputable def endpoint212 : EndpointCache :=
  { input := (439/256), certificate := { exponent := 0, mantissa := (439/256) }, enclosure := { lower := (11508646798710698196759351443143787609281269888/21339102556966908528778362945459457244873046875), upper := (2586775525101620298035972993134926146190747537057099/4796347403524338096196455082525031286015625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint212_valid : endpoint212.Valid 8 := by
  constructor
  · norm_num [endpoint212, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint212, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint212PositiveFacts : PositiveEndpointFacts 8
    endpoint212 :=
  { valid := endpoint212_valid
    positive := by
      norm_num [endpoint212] }

noncomputable def endpoint213 : EndpointCache :=
  { input := (445/256), certificate := { exponent := 0, mantissa := (445/256) }, enclosure := { lower := (1917433970137348843226655499696646420824605312/3467977820693700353699101305282778370769258215), upper := (87373631222863847593154127661759538843760494606163/158028813333370537717360648279125644799213558341120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint213_valid : endpoint213.Valid 8 := by
  constructor
  · norm_num [endpoint213, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint213, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint213PositiveFacts : PositiveEndpointFacts 8
    endpoint213 :=
  { valid := endpoint213_valid
    positive := by
      norm_num [endpoint213] }

noncomputable def endpoint214 : EndpointCache :=
  { input := (223/128), certificate := { exponent := 0, mantissa := (223/128) }, enclosure := { lower := (19391992177481736513111538653100305120640/34931619983494051173407193217611630575481), upper := (1107050050393935348416811342352486025611861945/1994176321617708393387469846407012766293059328) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint214_valid : endpoint214.Valid 8 := by
  constructor
  · norm_num [endpoint214, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint214, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint214PositiveFacts : PositiveEndpointFacts 8
    endpoint214 :=
  { valid := endpoint214_valid
    positive := by
      norm_num [endpoint214] }

noncomputable def endpoint215 : EndpointCache :=
  { input := (447/256), certificate := { exponent := 0, mantissa := (447/256) }, enclosure := { lower := (127095081486977302619716961766959736962271672448/228021850870451650535637232098101420648652618315), upper := (9695829585475417965621334378465141025377692030670489/17395330959205015516062693162299961178444410946014720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint215_valid : endpoint215.Valid 8 := by
  constructor
  · norm_num [endpoint215, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint215, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint215PositiveFacts : PositiveEndpointFacts 8
    endpoint215 :=
  { valid := endpoint215_valid
    positive := by
      norm_num [endpoint215] }

noncomputable def endpoint216 : EndpointCache :=
  { input := (453/256), certificate := { exponent := 0, mantissa := (453/256) }, enclosure := { lower := (147828838079876669541849601868768922068504289664/259024067562856863669725930873136004189637286705), upper := (11428943144852705295527071307229517090623471145526723/20025668711419589844033851167663890755909237909736960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint216_valid : endpoint216.Valid 8 := by
  constructor
  · norm_num [endpoint216, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint216, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint216PositiveFacts : PositiveEndpointFacts 8
    endpoint216 :=
  { valid := endpoint216_valid
    positive := by
      norm_num [endpoint216] }

noncomputable def endpoint217 : EndpointCache :=
  { input := (227/128), certificate := { exponent := 0, mantissa := (227/128) }, enclosure := { lower := (46722975107396680337337722167970559785856/81552389877941878540333111593780517578125), upper := (2715165533276427417660237029406072589057636917/4739172480586958445735837780937773437500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint217_valid : endpoint217.Valid 8 := by
  constructor
  · norm_num [endpoint217, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint217, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint217PositiveFacts : PositiveEndpointFacts 8
    endpoint217 :=
  { valid := endpoint217_valid
    positive := by
      norm_num [endpoint217] }

noncomputable def endpoint218 : EndpointCache :=
  { input := (229/128), certificate := { exponent := 0, mantissa := (229/128) }, enclosure := { lower := (243300742757574896191235742713740987964288/418264049848222545625466241026812174441485), upper := (2037608966974771538180638682660873749991324051/3502901665471742644963904701993690987779659520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint218_valid : endpoint218.Valid 8 := by
  constructor
  · norm_num [endpoint218, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint218, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint218PositiveFacts : PositiveEndpointFacts 8
    endpoint218 :=
  { valid := endpoint218_valid
    positive := by
      norm_num [endpoint218] }

noncomputable def endpoint219 : EndpointCache :=
  { input := (455/256), certificate := { exponent := 0, mantissa := (455/256) }, enclosure := { lower := (51799766107282698530391549540344838473700641152/90067757009164759889387030772771913332068207265), upper := (26521480286649381773807775219296519606330068861991/46114691588692357063366159755659219626018922119680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint219_valid : endpoint219.Valid 8 := by
  constructor
  · norm_num [endpoint219, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint219, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint219PositiveFacts : PositiveEndpointFacts 8
    endpoint219 :=
  { valid := endpoint219_valid
    positive := by
      norm_num [endpoint219] }

noncomputable def endpoint220 : EndpointCache :=
  { input := (233/128), certificate := { exponent := 0, mantissa := (233/128) }, enclosure := { lower := (19741348989943621601118571963250110884480/32956726359298915751507861275048460956343), upper := (1177531987829743335718996914805345049340197415/1965802813879461726745940909334090599123947264) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint220_valid : endpoint220.Valid 8 := by
  constructor
  · norm_num [endpoint220, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint220, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint220PositiveFacts : PositiveEndpointFacts 8
    endpoint220 :=
  { valid := endpoint220_valid
    positive := by
      norm_num [endpoint220] }

noncomputable def endpoint221 : EndpointCache :=
  { input := (463/256), certificate := { exponent := 0, mantissa := (463/256) }, enclosure := { lower := (21040795424701183647488139473249076579117472896/35508917880415084405909901452559378022137088995), upper := (4987846811971311068923110308724650656102389910622211/8417602037059678248927377598737915916415729768798720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint221_valid : endpoint221.Valid 8 := by
  constructor
  · norm_num [endpoint221, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint221, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint221PositiveFacts : PositiveEndpointFacts 8
    endpoint221 :=
  { valid := endpoint221_valid
    positive := by
      norm_num [endpoint221] }

noncomputable def endpoint222 : EndpointCache :=
  { input := (469/256), certificate := { exponent := 0, mantissa := (469/256) }, enclosure := { lower := (24352007179897319268532968859890374066080841088/40222974197686568952118740417063236236572265625), upper := (835371257032950814060977987737071719565967849975847/1379808906877440061333481271266937255859375000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint222_valid : endpoint222.Valid 8 := by
  constructor
  · norm_num [endpoint222, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint222, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint222PositiveFacts : PositiveEndpointFacts 8
    endpoint222 :=
  { valid := endpoint222_valid
    positive := by
      norm_num [endpoint222] }

noncomputable def endpoint223 : EndpointCache :=
  { input := (473/256), certificate := { exponent := 0, mantissa := (473/256) }, enclosure := { lower := (11493453645689498722238726784540485626126566784/18721481853548143153537047593477580144388908105), upper := (253039876486439828719586167064394745359768380634059/412172144487715919668271639818002404458866200839680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint223_valid : endpoint223.Valid 8 := by
  constructor
  · norm_num [endpoint223, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint223, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint223PositiveFacts : PositiveEndpointFacts 8
    endpoint223 :=
  { valid := endpoint223_valid
    positive := by
      norm_num [endpoint223] }

noncomputable def endpoint224 : EndpointCache :=
  { input := (1773/1024), certificate := { exponent := 0, mantissa := (1773/1024) }, enclosure := { lower := (17720398287021691918499688346664129012680431331156663936/32280150198524723354170238754145903106985149280980413455), upper := (2383133672180902299469855203749768269770674886893802355526117/4341206759498663595193369282264229827977266796102411230300160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint224_valid : endpoint224.Valid 8 := by
  constructor
  · norm_num [endpoint224, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint224, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint224PositiveFacts : PositiveEndpointFacts 8
    endpoint224 :=
  { valid := endpoint224_valid
    positive := by
      norm_num [endpoint224] }

noncomputable def endpoint225 : EndpointCache :=
  { input := (1793/1024), certificate := { exponent := 0, mantissa := (1793/1024) }, enclosure := { lower := (46951636202201876708609201409742624298494887555074310784/83816214303863202316157959832726423033646016540215401895), upper := (15673583019263144332137647090604558578771904450808099812668501/27979863923772829649989114783200065442783847825520866322196480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint225_valid : endpoint225.Valid 8 := by
  constructor
  · norm_num [endpoint225, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint225, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint225PositiveFacts : PositiveEndpointFacts 8
    endpoint225 :=
  { valid := endpoint225_valid
    positive := by
      norm_num [endpoint225] }

noncomputable def endpoint226 : EndpointCache :=
  { input := (1789/1024), certificate := { exponent := 0, mantissa := (1789/1024) }, enclosure := { lower := (3051882257155545589074105949956547162028998139434369920/5469908479738054974930063298711821187524737761842585757), upper := (11181705959825068949542676922861684646910048542561993601983365/20041044521474826957106960878377877717978635992957718362671104) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint226_valid : endpoint226.Valid 8 := by
  constructor
  · norm_num [endpoint226, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint226, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint226PositiveFacts : PositiveEndpointFacts 8
    endpoint226 :=
  { valid := endpoint226_valid
    positive := by
      norm_num [endpoint226] }

noncomputable def endpoint227 : EndpointCache :=
  { input := (1809/1024), certificate := { exponent := 0, mantissa := (1809/1024) }, enclosure := { lower := (31155268147067423879880325448990880851083301685334747520/54748875650987587564547204108297673168118242776068366113), upper := (12825003838542738877453176216514347023113420343286656906878585/22537265163977738445770727476772520564309538402282990773684224) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint227_valid : endpoint227.Valid 8 := by
  constructor
  · norm_num [endpoint227, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint227, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint227PositiveFacts : PositiveEndpointFacts 8
    endpoint227 :=
  { valid := endpoint227_valid
    positive := by
      norm_num [endpoint227] }

noncomputable def endpoint228 : EndpointCache :=
  { input := (901/512), certificate := { exponent := 0, mantissa := (901/512) }, enclosure := { lower := (1516509151357787601364129504769213044482159290720384/2683229155547196877053564166706273802366465694751355), upper := (1399167740868042777913632223588060732303232823019403618051/2475611616407576971494667585743209160634558045154274155520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint228_valid : endpoint228.Valid 8 := by
  constructor
  · norm_num [endpoint228, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint228, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint228PositiveFacts : PositiveEndpointFacts 8
    endpoint228 :=
  { valid := endpoint228_valid
    positive := by
      norm_num [endpoint228] }

noncomputable def endpoint229 : EndpointCache :=
  { input := (1821/1024), certificate := { exponent := 0, mantissa := (1821/1024) }, enclosure := { lower := (167901162139268003244162162514298656874560246904278887808/291662539065384499283597758178498771433391180572509765625), upper := (208723979414349106267896252015474812416499149494505046470422443/362576202163585824901414582710986248724620178652187500000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint229_valid : endpoint229.Valid 8 := by
  constructor
  · norm_num [endpoint229, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint229, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint229PositiveFacts : PositiveEndpointFacts 8
    endpoint229 :=
  { valid := endpoint229_valid
    positive := by
      norm_num [endpoint229] }

noncomputable def endpoint230 : EndpointCache :=
  { input := (1817/1024), certificate := { exponent := 0, mantissa := (1817/1024) }, enclosure := { lower := (4199150038853478769355479951377379265652821757929578624/7322350105349670264384870464842725234535223098222444155), upper := (15625944333381059918412711830560792209513194428755111964570699/27248046369628878582553210131700186626356224756674930748692480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint230_valid : endpoint230.Valid 8 := by
  constructor
  · norm_num [endpoint230, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint230, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint230PositiveFacts : PositiveEndpointFacts 8
    endpoint230 :=
  { valid := endpoint230_valid
    positive := by
      norm_num [endpoint230] }

noncomputable def endpoint231 : EndpointCache :=
  { input := (1837/1024), certificate := { exponent := 0, mantissa := (1837/1024) }, enclosure := { lower := (20601317587309766445642985120273064483644484858206955904/35251041179265470016888417841822038108337411930722409505), upper := (7045980249417016531184714682897161226217985018451632417729979/12056420099967658993296109116588606185661128278897955609262080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint231_valid : endpoint231.Valid 8 := by
  constructor
  · norm_num [endpoint231, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint231, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint231PositiveFacts : PositiveEndpointFacts 8
    endpoint231 :=
  { valid := endpoint231_valid
    positive := by
      norm_num [endpoint231] }

noncomputable def endpoint232 : EndpointCache :=
  { input := (1805/1024), certificate := { exponent := 0, mantissa := (1805/1024) }, enclosure := { lower := (4603524588411177008515677537634506778606415426561783168/8121324490489094594987830121710336343993028086779625385), upper := (3403514630986217646001946707974417132170291517027166701206557/6004322592904321328723162468223859548531677469342606876641280) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint232_valid : endpoint232.Valid 8 := by
  constructor
  · norm_num [endpoint232, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint232, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint232PositiveFacts : PositiveEndpointFacts 8
    endpoint232 :=
  { valid := endpoint232_valid
    positive := by
      norm_num [endpoint232] }

noncomputable def endpoint233 : EndpointCache :=
  { input := (7297/4096), certificate := { exponent := 0, mantissa := (7297/4096) }, enclosure := { lower := (1858228261158704462825968164430702983847607965439766844004545152/3217976419314869137982194635645215142167769686781408261656420935), upper := (111079355541719189357669528539005850937343732992007952805550844536140103/192361053648818996018020960307635281038526180593204724410834153985597440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint233_valid : endpoint233.Valid 8 := by
  constructor
  · norm_num [endpoint233, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint233, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint233PositiveFacts : PositiveEndpointFacts 8
    endpoint233 :=
  { valid := endpoint233_valid
    positive := by
      norm_num [endpoint233] }

noncomputable def endpoint234 : EndpointCache :=
  { input := (1833/1024), certificate := { exponent := 0, mantissa := (1833/1024) }, enclosure := { lower := (180884072504968773526698880580109533555762350600389933952/310670629199039772166982309979287847899086590649477208685), upper := (17411177314494517303676849214706002356158323617694151664598907/29903912084182772309705049229366331087374478869556078199183360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint234_valid : endpoint234.Valid 8 := by
  constructor
  · norm_num [endpoint234, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint234, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint234PositiveFacts : PositiveEndpointFacts 8
    endpoint234 :=
  { valid := endpoint234_valid
    positive := by
      norm_num [endpoint234] }

noncomputable def endpoint235 : EndpointCache :=
  { input := (1853/1024), certificate := { exponent := 0, mantissa := (1853/1024) }, enclosure := { lower := (9741938916070492727829957980753478546785714228213360512/16425750616429175024564480375029205528717617716124690485), upper := (5281444675198584957941659337297249719943152153529642049201019/8904971963902028454917261058904976192281964435157299629701120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint235_valid : endpoint235.Valid 8 := by
  constructor
  · norm_num [endpoint235, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint235, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint235PositiveFacts : PositiveEndpointFacts 8
    endpoint235 :=
  { valid := endpoint235_valid
    positive := by
      norm_num [endpoint235] }

noncomputable def endpoint236 : EndpointCache :=
  { input := (471/256), certificate := { exponent := 0, mantissa := (471/256) }, enclosure := { lower := (46003954052535652182863502613795227343039806080/75455821170040398412006309440715924189056175287), upper := (3697981856017912986954767229330169856141379789512845/6065440728932527385950715178082508850013091594270208) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint236_valid : endpoint236.Valid 8 := by
  constructor
  · norm_num [endpoint236, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint236, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint236PositiveFacts : PositiveEndpointFacts 8
    endpoint236 :=
  { valid := endpoint236_valid
    positive := by
      norm_num [endpoint236] }

noncomputable def endpoint237 : EndpointCache :=
  { input := (237/128), certificate := { exponent := 0, mantissa := (237/128) }, enclosure := { lower := (7544688850266230894650496464855652989814144/12247277496084231913357010131334381103515625), upper := (152583787957578410178176239913127196926801827291/247688940080807506215732172896106523437500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint237_valid : endpoint237.Valid 8 := by
  constructor
  · norm_num [endpoint237, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint237, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint237PositiveFacts : PositiveEndpointFacts 8
    endpoint237 :=
  { valid := endpoint237_valid
    positive := by
      norm_num [endpoint237] }

noncomputable def endpoint238 : EndpointCache :=
  { input := (475/256), certificate := { exponent := 0, mantissa := (475/256) }, enclosure := { lower := (28135181993193191806074418754732682037059590784/45516067853900598671194277735176938302858507255), upper := (1368495258286311207564924867362440519990987115934099/2213901540413725119366889669039006279051037792883200) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint238_valid : endpoint238.Valid 8 := by
  constructor
  · norm_num [endpoint238, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint238, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint238PositiveFacts : PositiveEndpointFacts 8
    endpoint238 :=
  { valid := endpoint238_valid
    positive := by
      norm_num [endpoint238] }

noncomputable def endpoint239 : EndpointCache :=
  { input := (943/512), certificate := { exponent := 0, mantissa := (943/512) }, enclosure := { lower := (2542891204976524647637084358140466458974659465889152/4163611854393202688644860860796648115929107666015625), upper := (2455497129219585605083755452119691384692555215020170994729/4020516842181417098641514282732788913480856093750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint239_valid : endpoint239.Valid 8 := by
  constructor
  · norm_num [endpoint239, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint239, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint239PositiveFacts : PositiveEndpointFacts 8
    endpoint239 :=
  { valid := endpoint239_valid
    positive := by
      norm_num [endpoint239] }

noncomputable def endpoint240 : EndpointCache :=
  { input := (953/512), certificate := { exponent := 0, mantissa := (953/512) }, enclosure := { lower := (136510158292953907564606131380758499060394515651712/219720415770597243492091192808050225776824951171875), upper := (133216441838962106530510876517570231928393624633839305779/214419001578884273201114016507977589929281718750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint240_valid : endpoint240.Valid 8 := by
  constructor
  · norm_num [endpoint240, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint240, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint240PositiveFacts : PositiveEndpointFacts 8
    endpoint240 :=
  { valid := endpoint240_valid
    positive := by
      norm_num [endpoint240] }

noncomputable def endpoint241 : EndpointCache :=
  { input := (477/256), certificate := { exponent := 0, mantissa := (477/256) }, enclosure := { lower := (20431013394224466246116252389475735356848128896/32829393427959554104744933108916726052359671005), upper := (61601775802302718147321238640380047111339399087349/98984268895678940020706500538173808684092448043520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint241_valid : endpoint241.Valid 8 := by
  constructor
  · norm_num [endpoint241, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint241, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint241PositiveFacts : PositiveEndpointFacts 8
    endpoint241 :=
  { valid := endpoint241_valid
    positive := by
      norm_num [endpoint241] }

noncomputable def endpoint242 : EndpointCache :=
  { input := (481/256), certificate := { exponent := 0, mantissa := (481/256) }, enclosure := { lower := (590023806411147593695842325571078628275740800/935521365092714056408111683899317459397042363), upper := (11177411056604561630627335228765140483365936449575/17722516740316375084595267739788669950817570524672) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint242_valid : endpoint242.Valid 8 := by
  constructor
  · norm_num [endpoint242, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint242, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint242PositiveFacts : PositiveEndpointFacts 8
    endpoint242 :=
  { valid := endpoint242_valid
    positive := by
      norm_num [endpoint242] }

noncomputable def endpoint243 : EndpointCache :=
  { input := (479/256), certificate := { exponent := 0, mantissa := (479/256) }, enclosure := { lower := (13263999824602960315783469491303251229530228352/21170805526962411483743090136334785003662109375), upper := (464709920982030211179422203905031775996503260505033/741728244839496784509289338536547621796875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint243_valid : endpoint243.Valid 8 := by
  constructor
  · norm_num [endpoint243, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint243, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint243PositiveFacts : PositiveEndpointFacts 8
    endpoint243 :=
  { valid := endpoint243_valid
    positive := by
      norm_num [endpoint243] }

noncomputable def endpoint244 : EndpointCache :=
  { input := (485/256), certificate := { exponent := 0, mantissa := (485/256) }, enclosure := { lower := (8228800912273533946252450215566017485795570304/12878198175260760625041028103680621771953611655), upper := (81735034306555669010968674833920631834929688306887/127916566835230083136407523948238879936460833846784) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint244_valid : endpoint244.Valid 8 := by
  constructor
  · norm_num [endpoint244, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint244, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint244PositiveFacts : PositiveEndpointFacts 8
    endpoint244 :=
  { valid := endpoint244_valid
    positive := by
      norm_num [endpoint244] }

noncomputable def endpoint245 : EndpointCache :=
  { input := (483/256), certificate := { exponent := 0, mantissa := (483/256) }, enclosure := { lower := (306180063632689767277305622525658065216542388864/482295452656651781136981597362440375582379944455), upper := (515082350505917819823000520319032014514638576855397/811358750069247339238442184362871123265443746557440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint245_valid : endpoint245.Valid 8 := by
  constructor
  · norm_num [endpoint245, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint245, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint245PositiveFacts : PositiveEndpointFacts 8
    endpoint245 :=
  { valid := endpoint245_valid
    positive := by
      norm_num [endpoint245] }

noncomputable def endpoint246 : EndpointCache :=
  { input := (489/256), certificate := { exponent := 0, mantissa := (489/256) }, enclosure := { lower := (352386413381074788966471054839540037513609476992/544490970998279064586245937894954489288330078125), upper := (29408760779113998218489850225901649757424590919640447/45441038475632377614109740992961321858046875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint246_valid : endpoint246.Valid 8 := by
  constructor
  · norm_num [endpoint246, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint246, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint246PositiveFacts : PositiveEndpointFacts 8
    endpoint246 :=
  { valid := endpoint246_valid
    positive := by
      norm_num [endpoint246] }

noncomputable def endpoint247 : EndpointCache :=
  { input := (487/256), certificate := { exponent := 0, mantissa := (487/256) }, enclosure := { lower := (485305346881860925096252431010006230790916736/754649976837277825403770068016135628571122455), upper := (121007977399910417198770501384054915240999324911399/188167443824514202097477643839415322170437957419520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint247_valid : endpoint247.Valid 8 := by
  constructor
  · norm_num [endpoint247, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint247, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint247PositiveFacts : PositiveEndpointFacts 8
    endpoint247 :=
  { valid := endpoint247_valid
    positive := by
      norm_num [endpoint247] }

noncomputable def endpoint248 : EndpointCache :=
  { input := (493/256), certificate := { exponent := 0, mantissa := (493/256) }, enclosure := { lower := (6137542365863952230772159339932982911495334528/9365550442404479403169659188436435153481480535), upper := (221316272944433572609056808954076611902683682562329/337716397209995581861496099101195887957311627246080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint248_valid : endpoint248.Valid 8 := by
  constructor
  · norm_num [endpoint248, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint248, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint248PositiveFacts : PositiveEndpointFacts 8
    endpoint248 :=
  { valid := endpoint248_valid
    positive := by
      norm_num [endpoint248] }

noncomputable def endpoint249 : EndpointCache :=
  { input := (491/256), certificate := { exponent := 0, mantissa := (491/256) }, enclosure := { lower := (24610657745449324958784104929505577397725127040/37788909505250281411065111173241960478885748529), upper := (6186922532997275302949623935232016600733764990355305/9499829538343878744490480428063642928708046094202368) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint249_valid : endpoint249.Valid 8 := by
  constructor
  · norm_num [endpoint249, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint249, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint249PositiveFacts : PositiveEndpointFacts 8
    endpoint249 :=
  { valid := endpoint249_valid
    positive := by
      norm_num [endpoint249] }

noncomputable def endpoint250 : EndpointCache :=
  { input := (497/256), certificate := { exponent := 0, mantissa := (497/256) }, enclosure := { lower := (141329779985126390270478564090927177037656754816/213034518802295477598212792103490758871079544855), upper := (5137620228964141031553436930650116814317672769296977/7744230827501045201650231418546096066481483614568960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint250_valid : endpoint250.Valid 8 := by
  constructor
  · norm_num [endpoint250, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint250, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint250PositiveFacts : PositiveEndpointFacts 8
    endpoint250 :=
  { valid := endpoint250_valid
    positive := by
      norm_num [endpoint250] }

noncomputable def endpoint251 : EndpointCache :=
  { input := (239/128), certificate := { exponent := 0, mantissa := (239/128) }, enclosure := { lower := (922318866292045568617710041593387387731072/1477049485156842547763012255917142433867715), upper := (56431157810261906134777686921022241936261901603/90371795699836254442332141866034442673762274560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint251_valid : endpoint251.Valid 8 := by
  constructor
  · norm_num [endpoint251, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint251, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint251PositiveFacts : PositiveEndpointFacts 8
    endpoint251 :=
  { valid := endpoint251_valid
    positive := by
      norm_num [endpoint251] }

noncomputable def endpoint252 : EndpointCache :=
  { input := (241/128), certificate := { exponent := 0, mantissa := (241/128) }, enclosure := { lower := (3042036521871086279420561233871226924317312/4807517003170213501810689911573118348675735), upper := (187681486452468127564172528227209067942544190647/296604569027589492207712324784415109639898146560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint252_valid : endpoint252.Valid 8 := by
  constructor
  · norm_num [endpoint252, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint252, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint252PositiveFacts : PositiveEndpointFacts 8
    endpoint252 :=
  { valid := endpoint252_valid
    positive := by
      norm_num [endpoint252] }

noncomputable def endpoint253 : EndpointCache :=
  { input := (951/512), certificate := { exponent := 0, mantissa := (951/512) }, enclosure := { lower := (109054677337719060394444246506624088843601381262976/176124899362324223328259200424676351531044003444095), upper := (5057145837735171276668668155662633900047997974200814259/8167364476029334498019937504493334445398447409997255680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint253_valid : endpoint253.Valid 8 := by
  constructor
  · norm_num [endpoint253, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint253, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint253PositiveFacts : PositiveEndpointFacts 8
    endpoint253 :=
  { valid := endpoint253_valid
    positive := by
      norm_num [endpoint253] }

noncomputable def endpoint254 : EndpointCache :=
  { input := (961/512), certificate := { exponent := 0, mantissa := (961/512) }, enclosure := { lower := (3152576237105858843838918449281793783863849198035584/5006872580044266921035552698682349907531905729162855), upper := (3102336800586904976057228712617429066609585032714890683111/4927083058608681483381930130876147979405477279462915742720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint254_valid : endpoint254.Valid 8 := by
  constructor
  · norm_num [endpoint254, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint254, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint254PositiveFacts : PositiveEndpointFacts 8
    endpoint254 :=
  { valid := endpoint254_valid
    positive := by
      norm_num [endpoint254] }

noncomputable def endpoint255 : EndpointCache :=
  { input := (959/512), certificate := { exponent := 0, mantissa := (959/512) }, enclosure := { lower := (1026251702082821311725483332519350217565350187578496/1635287709651976465893378817931580289873066745912755), upper := (143970799593753527729638367877749056101766063960001320053/229411242211656474447250327609985535705712787650608573440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint255_valid : endpoint255.Valid 8 := by
  constructor
  · norm_num [endpoint255, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint255, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint255PositiveFacts : PositiveEndpointFacts 8
    endpoint255 :=
  { valid := endpoint255_valid
    positive := by
      norm_num [endpoint255] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
