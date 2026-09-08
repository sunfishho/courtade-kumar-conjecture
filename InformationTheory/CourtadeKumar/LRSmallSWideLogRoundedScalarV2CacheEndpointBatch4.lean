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

noncomputable def endpoint256 : EndpointCache :=
  { input := (969/512), certificate := { exponent := 0, mantissa := (969/512) }, enclosure := { lower := (10393272017692181284711713991285002597968753394568064/16291927510862730362629150262782229905234820776884045), upper := (3437595531232815870780059724541134899303030881775423981983/5388587608072869792900316707715748105616227441595951651840) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint256_valid : endpoint256.Valid 8 := by
  constructor
  · norm_num [endpoint256, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint256, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint256PositiveFacts : PositiveEndpointFacts 8
    endpoint256 :=
  { valid := endpoint256_valid
    positive := by
      norm_num [endpoint256] }

noncomputable def endpoint257 : EndpointCache :=
  { input := (243/128), certificate := { exponent := 0, mantissa := (243/128) }, enclosure := { lower := (286461554832866381821093200288006942962560/446876164777451728992900273574766982380637), upper := (282860326056197136811209510172035493409791835/441258292991678050114132384421255626030708992) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint257_valid : endpoint257.Valid 8 := by
  constructor
  · norm_num [endpoint257, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint257, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint257PositiveFacts : PositiveEndpointFacts 8
    endpoint257 :=
  { valid := endpoint257_valid
    positive := by
      norm_num [endpoint257] }

noncomputable def endpoint258 : EndpointCache :=
  { input := (245/128), certificate := { exponent := 0, mantissa := (245/128) }, enclosure := { lower := (94078506115632554302921713314809647739776/144908281684710481278371384082019042812445), upper := (168588684546123676028154592400748948077959239/259675640779001182450841520274978124719901440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint258_valid : endpoint258.Valid 8 := by
  constructor
  · norm_num [endpoint258, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint258, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint258PositiveFacts : PositiveEndpointFacts 8
    endpoint258 :=
  { valid := endpoint258_valid
    positive := by
      norm_num [endpoint258] }

noncomputable def endpoint259 : EndpointCache :=
  { input := (1937/1024), certificate := { exponent := 0, mantissa := (1937/1024) }, enclosure := { lower := (1465679577263956839276345955806595105118884014787888256/2299379855209586940402918785923996137648256348068018195), upper := (63893579650497597208454538979332430838268970287172462496201/100237194510987982005404496194611324199377245875093126891520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint259_valid : endpoint259.Valid 8 := by
  constructor
  · norm_num [endpoint259, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint259, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint259PositiveFacts : PositiveEndpointFacts 8
    endpoint259 :=
  { valid := endpoint259_valid
    positive := by
      norm_num [endpoint259] }

noncomputable def endpoint260 : EndpointCache :=
  { input := (1957/1024), certificate := { exponent := 0, mantissa := (1957/1024) }, enclosure := { lower := (3844256526749670160672230421790565643523173050207502464/5935277612449242392774001548858136273533689690819248955), upper := (15407534266753485698383180902542226821520799152279428800262019/23788212812929366758725060671724283263601522124663337379706880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint260_valid : endpoint260.Valid 8 := by
  constructor
  · norm_num [endpoint260, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint260, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint260PositiveFacts : PositiveEndpointFacts 8
    endpoint260 :=
  { valid := endpoint260_valid
    positive := by
      norm_num [endpoint260] }

noncomputable def endpoint261 : EndpointCache :=
  { input := (1953/1024), certificate := { exponent := 0, mantissa := (1953/1024) }, enclosure := { lower := (28601117229221439270423557890144670099484304580314731904/44298167264119512703090763624176843155289210393527296745), upper := (1815827746375229191989304120857454703426999760468152115338647/2812402043264419622493826400971739418243001389464261015746560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint261_valid : endpoint261.Valid 8 := by
  constructor
  · norm_num [endpoint261, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint261, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint261PositiveFacts : PositiveEndpointFacts 8
    endpoint261 :=
  { valid := endpoint261_valid
    positive := by
      norm_num [endpoint261] }

noncomputable def endpoint262 : EndpointCache :=
  { input := (1973/1024), certificate := { exponent := 0, mantissa := (1973/1024) }, enclosure := { lower := (10707304869463247621906917695903189145382502245954071168/16326125416784516038069497092577679203670911056815787415), upper := (43265050089619114731779299756278459112999592639513502888774367/65969040276102861093091569179966998668989864990919779470940160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint262_valid : endpoint262.Valid 8 := by
  constructor
  · norm_num [endpoint262, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint262, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint262PositiveFacts : PositiveEndpointFacts 8
    endpoint262 :=
  { valid := endpoint262_valid
    positive := by
      norm_num [endpoint262] }

noncomputable def endpoint263 : EndpointCache :=
  { input := (7827/4096), certificate := { exponent := 0, mantissa := (7827/4096) }, enclosure := { lower := (4484086799057475834365768251532784428674255046761547986406393728/6924499021811659303353186999748539903926964890172890358284542965), upper := (95838065169992813310302307345563849335796318428606621499598143884534399/147996819029251023851097824316161561471757937856193093179509740303851520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint263_valid : endpoint263.Valid 8 := by
  constructor
  · norm_num [endpoint263, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint263, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint263PositiveFacts : PositiveEndpointFacts 8
    endpoint263 :=
  { valid := endpoint263_valid
    positive := by
      norm_num [endpoint263] }

noncomputable def endpoint264 : EndpointCache :=
  { input := (3953/2048), certificate := { exponent := 0, mantissa := (3953/2048) }, enclosure := { lower := (310282726325620775296815557932800751763809648549734805810560/471833181220644285534308022817192278329730235422063870091001), upper := (5023939097273802676813006758895053717612159281815476249653709778905/7639681291735887301497321939748294968268487150073522087812001599488) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint264_valid : endpoint264.Valid 8 := by
  constructor
  · norm_num [endpoint264, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint264, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint264PositiveFacts : PositiveEndpointFacts 8
    endpoint264 :=
  { valid := endpoint264_valid
    positive := by
      norm_num [endpoint264] }

noncomputable def endpoint265 : EndpointCache :=
  { input := (495/256), certificate := { exponent := 0, mantissa := (495/256) }, enclosure := { lower := (404931559170001975276548989187705587073938198656/614109260378582131385247419487321302216836488795), upper := (207324960759977356269626952369878344996619656745461/314423941313834051269246678777508506735020282263040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint265_valid : endpoint265.Valid 8 := by
  constructor
  · norm_num [endpoint265, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint265, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint265PositiveFacts : PositiveEndpointFacts 8
    endpoint265 :=
  { valid := endpoint265_valid
    positive := by
      norm_num [endpoint265] }

noncomputable def endpoint266 : EndpointCache :=
  { input := (501/256), certificate := { exponent := 0, mantissa := (501/256) }, enclosure := { lower := (13274452323435307687253540536648693554705365120/19770458417114280005736188621804075508035442891), upper := (1135018789175547750732027732535611193918965283361105/1690453276496939397610467071918735672239062508952064) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint266_valid : endpoint266.Valid 8 := by
  constructor
  · norm_num [endpoint266, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint266, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint266PositiveFacts : PositiveEndpointFacts 8
    endpoint266 :=
  { valid := endpoint266_valid
    positive := by
      norm_num [endpoint266] }

noncomputable def endpoint267 : EndpointCache :=
  { input := (127/64), certificate := { exponent := 0, mantissa := (127/64) }, enclosure := { lower := (8048034300594473287261181001835212672/11743743322836501713465086995056670965), upper := (130828848364393023473523376931714798885877/190906291456030171854088454191641243207040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint267_valid : endpoint267.Valid 8 := by
  constructor
  · norm_num [endpoint267, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint267, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint267PositiveFacts : PositiveEndpointFacts 8
    endpoint267 :=
  { valid := endpoint267_valid
    positive := by
      norm_num [endpoint267] }

noncomputable def endpoint268 : EndpointCache :=
  { input := (499/256), certificate := { exponent := 0, mantissa := (499/256) }, enclosure := { lower := (49318879596783605254197442228551896775345948288/73893860480353581210558267440260429534912109375), upper := (12600382090190365205353123245958408504496047928004759/18878994626404575756323110631777256621015625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint268_valid : endpoint268.Valid 8 := by
  constructor
  · norm_num [endpoint268, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint268, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint268PositiveFacts : PositiveEndpointFacts 8
    endpoint268 :=
  { valid := endpoint268_valid
    positive := by
      norm_num [endpoint268] }

noncomputable def endpoint269 : EndpointCache :=
  { input := (505/256), certificate := { exponent := 0, mantissa := (505/256) }, enclosure := { lower := (56531084894330313192910466798823753420666816384/83209695620890828781163202950035858891646702005), upper := (2923335516483684600533432388154453957074446404602657/4302939779947506537931511550952254335004834254082560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint269_valid : endpoint269.Valid 8 := by
  constructor
  · norm_num [endpoint269, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint269, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint269PositiveFacts : PositiveEndpointFacts 8
    endpoint269 :=
  { valid := endpoint269_valid
    positive := by
      norm_num [endpoint269] }

noncomputable def endpoint270 : EndpointCache :=
  { input := (1989/1024), certificate := { exponent := 0, mantissa := (1989/1024) }, enclosure := { lower := (91574878715590417523576422921233622834221432385328247680/137931532664615243071371347452902548648977055225965674813), upper := (354252335486877733764261341894839440964754056303820164901945/533580471250138255863651648102250570418087239416357881587712) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint270_valid : endpoint270.Valid 8 := by
  constructor
  · norm_num [endpoint270, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint270, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint270PositiveFacts : PositiveEndpointFacts 8
    endpoint270 :=
  { valid := endpoint270_valid
    positive := by
      norm_num [endpoint270] }

noncomputable def endpoint271 : EndpointCache :=
  { input := (1993/1024), certificate := { exponent := 0, mantissa := (1993/1024) }, enclosure := { lower := (7436364978647415523359327116657658698660057648629912704/11166978871361423906155460356412697424435852311883866995), upper := (4336106234688079130686268409043476832465955606914227313619013/6511407949713793563784874420028125174316076955819021727754240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint271_valid : endpoint271.Valid 8 := by
  constructor
  · norm_num [endpoint271, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint271, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint271PositiveFacts : PositiveEndpointFacts 8
    endpoint271 :=
  { valid := endpoint271_valid
    positive := by
      norm_num [endpoint271] }

noncomputable def endpoint272 : EndpointCache :=
  { input := (2009/1024), certificate := { exponent := 0, mantissa := (2009/1024) }, enclosure := { lower := (34217650964171498272607000881665106854342791225107264640/50774012647436082912453231607823643834462732019703416371), upper := (20112314344914443906927857737147296713380457895339371457993765/29843746057859391069950110661520150078445166775613195260880896) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint272_valid : endpoint272.Valid 8 := by
  constructor
  · norm_num [endpoint272, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint272, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint272PositiveFacts : PositiveEndpointFacts 8
    endpoint272 :=
  { valid := endpoint272_valid
    positive := by
      norm_num [endpoint272] }

noncomputable def endpoint273 : EndpointCache :=
  { input := (249/128), certificate := { exponent := 0, mantissa := (249/128) }, enclosure := { lower := (92582387192117455388302512483642138948736/139133210590381290424539515162511860643795), upper := (1967190589883165047061070188109469973119788833/2956302458624421658940615618173052014959356160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint273_valid : endpoint273.Valid 8 := by
  constructor
  · norm_num [endpoint273, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint273, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint273PositiveFacts : PositiveEndpointFacts 8
    endpoint273 :=
  { valid := endpoint273_valid
    positive := by
      norm_num [endpoint273] }

noncomputable def endpoint274 : EndpointCache :=
  { input := (2013/1024), certificate := { exponent := 0, mantissa := (2013/1024) }, enclosure := { lower := (525057779144174215057907193274780675361013665203462049152/776816550767371866393128213537859292849584307442321392185), upper := (65594419363941635435980725311564045737284974887103145696468641/97046138054266232524760721460857685737112868360154326882887680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint274_valid : endpoint274.Valid 8 := by
  constructor
  · norm_num [endpoint274, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint274, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint274PositiveFacts : PositiveEndpointFacts 8
    endpoint274 :=
  { valid := endpoint274_valid
    positive := by
      norm_num [endpoint274] }

noncomputable def endpoint275 : EndpointCache :=
  { input := (253/128), certificate := { exponent := 0, mantissa := (253/128) }, enclosure := { lower := (1058780921411643297293187569525871133072000/1553924690615749858725590602354499659286103), upper := (566736562409828183957216602148082489731410375/831773507122321378925116133333026726716052224) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint275_valid : endpoint275.Valid 8 := by
  constructor
  · norm_num [endpoint275, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint275, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint275PositiveFacts : PositiveEndpointFacts 8
    endpoint275 :=
  { valid := endpoint275_valid
    positive := by
      norm_num [endpoint275] }

noncomputable def endpoint276 : EndpointCache :=
  { input := (507/256), certificate := { exponent := 0, mantissa := (507/256) }, enclosure := { lower := (76041271449198590313883978292664913953890299264/111279872801450766557718530811820452870966127545), upper := (72304387577791798925681165821963785419132355014657/105811261909493757458310648726210990615592934991360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint276_valid : endpoint276.Valid 8 := by
  constructor
  · norm_num [endpoint276, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint276, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint276PositiveFacts : PositiveEndpointFacts 8
    endpoint276 :=
  { valid := endpoint276_valid
    positive := by
      norm_num [endpoint276] }

noncomputable def endpoint277 : EndpointCache :=
  { input := (509/256), certificate := { exponent := 0, mantissa := (509/256) }, enclosure := { lower := (16872596728240675375110486184284275071312317824/24550151622360989847220743264880731353759765625), upper := (4397133785468732322262122358245330490112980057500737/6397965914000252842104503460774037636640625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint277_valid : endpoint277.Valid 8 := by
  constructor
  · norm_num [endpoint277, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint277, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint277PositiveFacts : PositiveEndpointFacts 8
    endpoint277 :=
  { valid := endpoint277_valid
    positive := by
      norm_num [endpoint277] }

noncomputable def endpoint278 : EndpointCache :=
  { input := (255/128), certificate := { exponent := 0, mantissa := (255/128) }, enclosure := { lower := (17377785825466470620049849968878214004516992/25213213467494311245869656266899743456434315), upper := (15125625131826231765955348770722625520319360705/21945581002107048508404948814709536704480427776) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint278_valid : endpoint278.Valid 8 := by
  constructor
  · norm_num [endpoint278, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint278, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint278PositiveFacts : PositiveEndpointFacts 8
    endpoint278 :=
  { valid := endpoint278_valid
    positive := by
      norm_num [endpoint278] }

noncomputable def endpoint279 : EndpointCache :=
  { input := (2029/1024), certificate := { exponent := 0, mantissa := (2029/1024) }, enclosure := { lower := (12772681712963484004639556818453626257358040530126445440/18678248194397394096851214717204751449066099681698250157), upper := (53075500498169751264443499970458832882957639346055652528015605/77615443121013376250902762826154886533437678088531455116396544) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint279_valid : endpoint279.Valid 8 := by
  constructor
  · norm_num [endpoint279, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint279, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint279PositiveFacts : PositiveEndpointFacts 8
    endpoint279 :=
  { valid := endpoint279_valid
    positive := by
      norm_num [endpoint279] }

noncomputable def endpoint280 : EndpointCache :=
  { input := (1947/1024), certificate := { exponent := 0, mantissa := (1947/1024) }, enclosure := { lower := (27616308401191420965873356022975719470086804404131334272/42977684758569742727202901525189670460588099442862036715), upper := (3336933803624459228792858347171457794364668190762931123441619/5193079604747499153213380997091718261093781231879905620346880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint280_valid : endpoint280.Valid 8 := by
  constructor
  · norm_num [endpoint280, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint280, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint280PositiveFacts : PositiveEndpointFacts 8
    endpoint280 :=
  { valid := endpoint280_valid
    positive := by
      norm_num [endpoint280] }

noncomputable def endpoint281 : EndpointCache :=
  { input := (1005/512), certificate := { exponent := 0, mantissa := (1005/512) }, enclosure := { lower := (15752866098110685714729361736902720213779921673524608/23357712202268261312000816184425901908928108311758185), upper := (1080772655287402522740258752068605497689248480542837048543/1602525918773220872093751996781092278167739655053105556480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint281_valid : endpoint281.Valid 8 := by
  constructor
  · norm_num [endpoint281, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint281, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint281PositiveFacts : PositiveEndpointFacts 8
    endpoint281 :=
  { valid := endpoint281_valid
    positive := by
      norm_num [endpoint281] }

noncomputable def endpoint282 : EndpointCache :=
  { input := (1037/512), certificate := { exponent := 1, mantissa := (1037/1024) }, enclosure := { lower := (15569899104089201460219511323533493809931455201096000/22061100286775141362185983086561271009301032693138529), upper := (33066978855999810742330724202734358800761593007685026044425/46852835322646162621617898415644749899049310008902972565504) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint282_valid : endpoint282.Valid 8 := by
  constructor
  · norm_num [endpoint282, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint282, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint282PositiveFacts : PositiveEndpointFacts 8
    endpoint282 :=
  { valid := endpoint282_valid
    positive := by
      norm_num [endpoint282] }

noncomputable def endpoint283 : EndpointCache :=
  { input := (129/64), certificate := { exponent := 1, mantissa := (129/128) }, enclosure := { lower := (3274174920926721781963212062831922920991553600/4671191270714784461656951988065220580038672781), upper := (36042118425456655854784579352128096124236943859055/51420473508028347353919727484621948145065709973248) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint283_valid : endpoint283.Valid 8 := by
  constructor
  · norm_num [endpoint283, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint283, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint283PositiveFacts : PositiveEndpointFacts 8
    endpoint283 :=
  { valid := endpoint283_valid
    positive := by
      norm_num [endpoint283] }

noncomputable def endpoint284 : EndpointCache :=
  { input := (67/32), certificate := { exponent := 1, mantissa := (67/64) }, enclosure := { lower := (261194812994755361301434698712906600449600/353464292952409599453331613516380775160453), upper := (2240006769057319547664606072826781463208764365/3031309776359864724911771917516481527776044928) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint284_valid : endpoint284.Valid 8 := by
  constructor
  · norm_num [endpoint284, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint284, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint284PositiveFacts : PositiveEndpointFacts 8
    endpoint284 :=
  { valid := endpoint284_valid
    positive := by
      norm_num [endpoint284] }

noncomputable def endpoint285 : EndpointCache :=
  { input := (259/128), certificate := { exponent := 1, mantissa := (259/256) }, enclosure := { lower := (7219666403208042350055915961559034413098591888442048/10243599563326017023576886331272556740485687255859375), upper := (19538480531910778808693828213119807027596978224426193751/27722107161092580927805790665661044984537265625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint285_valid : endpoint285.Valid 8 := by
  constructor
  · norm_num [endpoint285, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint285, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint285PositiveFacts : PositiveEndpointFacts 8
    endpoint285 :=
  { valid := endpoint285_valid
    positive := by
      norm_num [endpoint285] }

noncomputable def endpoint286 : EndpointCache :=
  { input := (535/256), certificate := { exponent := 1, mantissa := (535/512) }, enclosure := { lower := (489816212217635859127250723934195699655450010176/664527637674495143395854675791710180790613197781), upper := (268340920044211235151681285895444183359048378464477221/364054821023595419357985025585730505444329534272343040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint286_valid : endpoint286.Valid 8 := by
  constructor
  · norm_num [endpoint286, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint286, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint286PositiveFacts : PositiveEndpointFacts 8
    endpoint286 :=
  { valid := endpoint286_valid
    positive := by
      norm_num [endpoint286] }

noncomputable def endpoint287 : EndpointCache :=
  { input := (995/512), certificate := { exponent := 0, mantissa := (995/512) }, enclosure := { lower := (20279330067998793577041398804773059138210904496256/30521940497730116418207822763021843671651158558795), upper := (826488163804589093258167632569587648320162231142455771/1243927789373090440647343458271507843206877297295401984) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint287_valid : endpoint287.Valid 8 := by
  constructor
  · norm_num [endpoint287, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint287, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint287PositiveFacts : PositiveEndpointFacts 8
    endpoint287 :=
  { valid := endpoint287_valid
    positive := by
      norm_num [endpoint287] }

noncomputable def endpoint288 : EndpointCache :=
  { input := (525/256), certificate := { exponent := 1, mantissa := (525/512) }, enclosure := { lower := (53372001247899836796832982212876377837088465272330246208/74311409495726362563913439369765547146465103876128469453), upper := (1366323265091131162992403528049894724849834127961865574650433/1902372083090594881636184047865998006949506659228888817996800) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint288_valid : endpoint288.Valid 8 := by
  constructor
  · norm_num [endpoint288, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint288, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint288PositiveFacts : PositiveEndpointFacts 8
    endpoint288 :=
  { valid := endpoint288_valid
    positive := by
      norm_num [endpoint288] }

noncomputable def endpoint289 : EndpointCache :=
  { input := (137/64), certificate := { exponent := 1, mantissa := (137/128) }, enclosure := { lower := (365992981030035187022732744326961272196943017536/480875074260519346961888687247525054473876953125), upper := (12836106124527472163413175752421227022219251681118837/16865250604464934536647360039145198710507812500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint289_valid : endpoint289.Valid 8 := by
  constructor
  · norm_num [endpoint289, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint289, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint289PositiveFacts : PositiveEndpointFacts 8
    endpoint289 :=
  { valid := endpoint289_valid
    positive := by
      norm_num [endpoint289] }

noncomputable def endpoint290 : EndpointCache :=
  { input := (287/128), certificate := { exponent := 1, mantissa := (287/256) }, enclosure := { lower := (1275379607182069916818784563033363345098420032/1579511456841191178523886425192548711575082105), upper := (26772769291659917264734791593219363140545448138559/33157104502010285219573423837641982553384123548160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint290_valid : endpoint290.Valid 8 := by
  constructor
  · norm_num [endpoint290, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint290, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint290PositiveFacts : PositiveEndpointFacts 8
    endpoint290 :=
  { valid := endpoint290_valid
    positive := by
      norm_num [endpoint290] }

noncomputable def endpoint291 : EndpointCache :=
  { input := (141/64), certificate := { exponent := 1, mantissa := (141/128) }, enclosure := { lower := (6175853616414279858661850395368363356633771584/7818755493829719474416860058082067645489098885), upper := (74307872351763376612037527408775651843335333860143/94075266101759184716183660218843437910524837784320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint291_valid : endpoint291.Valid 8 := by
  constructor
  · norm_num [endpoint291, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint291, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint291PositiveFacts : PositiveEndpointFacts 8
    endpoint291 :=
  { valid := endpoint291_valid
    positive := by
      norm_num [endpoint291] }

noncomputable def endpoint292 : EndpointCache :=
  { input := (145/64), certificate := { exponent := 1, mantissa := (145/128) }, enclosure := { lower := (1161830127650590650729113151489284416/1420589585905425414460640711166315201), upper := (6161019322448690642672903283470541735703/7533183632687055912111283314070517180160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint292_valid : endpoint292.Valid 8 := by
  constructor
  · norm_num [endpoint292, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint292, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint292PositiveFacts : PositiveEndpointFacts 8
    endpoint292 :=
  { valid := endpoint292_valid
    positive := by
      norm_num [endpoint292] }

noncomputable def endpoint293 : EndpointCache :=
  { input := (573/256), certificate := { exponent := 1, mantissa := (573/512) }, enclosure := { lower := (84308237856988901130355526082139978191856855617592309952/104638664971089734302965308476574053906451519622802734375), upper := (2355620392798982553684024078454659817768205728756013858491939/2923664092815087799130166699011751394177059144843750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint293_valid : endpoint293.Valid 8 := by
  constructor
  · norm_num [endpoint293, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint293, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint293PositiveFacts : PositiveEndpointFacts 8
    endpoint293 :=
  { valid := endpoint293_valid
    positive := by
      norm_num [endpoint293] }

noncomputable def endpoint294 : EndpointCache :=
  { input := (293/128), certificate := { exponent := 1, mantissa := (293/256) }, enclosure := { lower := (28044829568037681622684129505664493971342400/33864745316215723202190772058896004507964477), upper := (4207173240991643490471142007757830441884413007285/5080253633357417931899850861187343012266798981632) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint294_valid : endpoint294.Valid 8 := by
  constructor
  · norm_num [endpoint294, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint294, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint294PositiveFacts : PositiveEndpointFacts 8
    endpoint294 :=
  { valid := endpoint294_valid
    positive := by
      norm_num [endpoint294] }

noncomputable def endpoint295 : EndpointCache :=
  { input := (73/32), certificate := { exponent := 1, mantissa := (73/64) }, enclosure := { lower := (19973816424278854347104018064052527777152576/24218802447150326002082473536466753369689765), upper := (186635344611279177123179512739922775492802121109/226300490066172646163458632724745343486381164160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint295_valid : endpoint295.Valid 8 := by
  constructor
  · norm_num [endpoint295, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint295, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint295PositiveFacts : PositiveEndpointFacts 8
    endpoint295 :=
  { valid := endpoint295_valid
    positive := by
      norm_num [endpoint295] }

noncomputable def endpoint296 : EndpointCache :=
  { input := (149/64), certificate := { exponent := 1, mantissa := (149/128) }, enclosure := { lower := (157928274341195767435802109143043415122303233600/186883383762726954045898439705141868762560798853), upper := (6024016220669574634640967655286330611622032885136605/7128479790245456935126750084112931442079119111448832) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint296_valid : endpoint296.Valid 8 := by
  constructor
  · norm_num [endpoint296, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint296, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint296PositiveFacts : PositiveEndpointFacts 8
    endpoint296 :=
  { valid := endpoint296_valid
    positive := by
      norm_num [endpoint296] }

noncomputable def endpoint297 : EndpointCache :=
  { input := (75/32), certificate := { exponent := 1, mantissa := (75/64) }, enclosure := { lower := (5127544353793192170994637342897999363486144/6019995363967900828767634460180030900348379), upper := (16408142267773276996054700677126187123271153697/19263985164697282652056430272576098881114812800) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint297_valid : endpoint297.Valid 8 := by
  constructor
  · norm_num [endpoint297, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint297, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint297PositiveFacts : PositiveEndpointFacts 8
    endpoint297 :=
  { valid := endpoint297_valid
    positive := by
      norm_num [endpoint297] }

noncomputable def endpoint298 : EndpointCache :=
  { input := (147/64), certificate := { exponent := 1, mantissa := (147/128) }, enclosure := { lower := (63362162015876446603990360840534636565090829376/76197703001975360365415741689503192901611328125), upper := (113544996711486915078050083117052244777071693455537/136546283779539845774825009107589721679687500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint298_valid : endpoint298.Valid 8 := by
  constructor
  · norm_num [endpoint298, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint298, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint298PositiveFacts : PositiveEndpointFacts 8
    endpoint298 :=
  { valid := endpoint298_valid
    positive := by
      norm_num [endpoint298] }

noncomputable def endpoint299 : EndpointCache :=
  { input := (151/64), certificate := { exponent := 1, mantissa := (151/128) }, enclosure := { lower := (62269653851117257374739345957038820169024/72541809686322587659571399473335721967985), upper := (2407095788125753823160780666917880872051171009/2804176195234485948568392018041265668394428160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint299_valid : endpoint299.Valid 8 := by
  constructor
  · norm_num [endpoint299, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint299, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint299PositiveFacts : PositiveEndpointFacts 8
    endpoint299 :=
  { valid := endpoint299_valid
    positive := by
      norm_num [endpoint299] }

noncomputable def endpoint300 : EndpointCache :=
  { input := (2343/1024), certificate := { exponent := 1, mantissa := (2343/2048) }, enclosure := { lower := (775669778866010440825693407401010593480390123683638977985176071616/937121094461669679366230575013453713714493037265099205906919605355), upper := (225577187158965421171690073329317910439817087134940976712050319648832091/272529808206964929474569710903112555207594007125287090665026731950919680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint300_valid : endpoint300.Valid 8 := by
  constructor
  · norm_num [endpoint300, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint300, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint300PositiveFacts : PositiveEndpointFacts 8
    endpoint300 :=
  { valid := endpoint300_valid
    positive := by
      norm_num [endpoint300] }

noncomputable def endpoint301 : EndpointCache :=
  { input := (2397/1024), certificate := { exponent := 1, mantissa := (2397/2048) }, enclosure := { lower := (136772140568784566726354449410783249285626603072912388063585222848/160813534339194565292542677826114748129721727646227637786865234375), upper := (63944962956803725805951539784497876950748902455444163530937279870053891/75185013869431344373023655984605291523304688136388539299375000000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint301_valid : endpoint301.Valid 8 := by
  constructor
  · norm_num [endpoint301, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint301, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint301PositiveFacts : PositiveEndpointFacts 8
    endpoint301 :=
  { valid := endpoint301_valid
    positive := by
      norm_num [endpoint301] }

noncomputable def endpoint302 : EndpointCache :=
  { input := (591/256), certificate := { exponent := 1, mantissa := (591/512) }, enclosure := { lower := (156871743272742398311772454650259727570087497100314923200/187502403712641226222982710757519860589405805881390589447), upper := (31645423685937125262621829095669711801234638557931293031135885/37824484896143689283509856275692966436979654408841160827964416) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint302_valid : endpoint302.Valid 8 := by
  constructor
  · norm_num [endpoint302, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint302, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint302PositiveFacts : PositiveEndpointFacts 8
    endpoint302 :=
  { valid := endpoint302_valid
    positive := by
      norm_num [endpoint302] }

noncomputable def endpoint303 : EndpointCache :=
  { input := (605/256), certificate := { exponent := 1, mantissa := (605/512) }, enclosure := { lower := (194848003965366603966577377336445918892949600302575350848/226554007988451418265518442906206765166544818769241616253), upper := (10973839805637699090831006184269044762874631248841290136853903/12759521729909583876713998704477565014179804193083687827368960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint303_valid : endpoint303.Valid 8 := by
  constructor
  · norm_num [endpoint303, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint303, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint303PositiveFacts : PositiveEndpointFacts 8
    endpoint303 :=
  { valid := endpoint303_valid
    positive := by
      norm_num [endpoint303] }

noncomputable def endpoint304 : EndpointCache :=
  { input := (153/64), certificate := { exponent := 1, mantissa := (153/128) }, enclosure := { lower := (1009796063664168357451100169425581559671863358016/1158614490759539419847707511089503971565588139605), upper := (4394632556917930224903786369675612430846392380234077/5042290263785515555177223088261521284253439583560960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint304_valid : endpoint304.Valid 8 := by
  constructor
  · norm_num [endpoint304, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint304, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint304PositiveFacts : PositiveEndpointFacts 8
    endpoint304 :=
  { valid := endpoint304_valid
    positive := by
      norm_num [endpoint304] }

noncomputable def endpoint305 : EndpointCache :=
  { input := (77/32), certificate := { exponent := 1, mantissa := (77/64) }, enclosure := { lower := (50714063907691198807136665239915200/57756319819373120800214445478760367), upper := (927342901284123563232091515553080805/1056115562411394208918207003040189568) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint305_valid : endpoint305.Valid 8 := by
  constructor
  · norm_num [endpoint305, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint305, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint305PositiveFacts : PositiveEndpointFacts 8
    endpoint305 :=
  { valid := endpoint305_valid
    positive := by
      norm_num [endpoint305] }

noncomputable def endpoint306 : EndpointCache :=
  { input := (599/256), certificate := { exponent := 1, mantissa := (599/512) }, enclosure := { lower := (11535229416874905072544800586077887101759522299830503616/13569514713650427286560979838397954219339203908612896615), upper := (7075433023819846822397187998275880361082743499463386514232151/8323214657000044487321627569357183567241403536649344074122240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint306_valid : endpoint306.Valid 8 := by
  constructor
  · norm_num [endpoint306, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint306, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint306PositiveFacts : PositiveEndpointFacts 8
    endpoint306 :=
  { valid := endpoint306_valid
    positive := by
      norm_num [endpoint306] }

noncomputable def endpoint307 : EndpointCache :=
  { input := (1225/512), certificate := { exponent := 1, mantissa := (1225/1024) }, enclosure := { lower := (550774848406410250583116220049524543086507666842214294439488/631353557912163665424973898380024388290041840424052424413733), upper := (197397709611267737159860974057706224838442725925806150276481320931/226277115155719457688310645179400740763150995607980388909881907200) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint307_valid : endpoint307.Valid 8 := by
  constructor
  · norm_num [endpoint307, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint307, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint307PositiveFacts : PositiveEndpointFacts 8
    endpoint307 :=
  { valid := endpoint307_valid
    positive := by
      norm_num [endpoint307] }

noncomputable def endpoint308 : EndpointCache :=
  { input := (155/64), certificate := { exponent := 1, mantissa := (155/128) }, enclosure := { lower := (2505230950626108735769083465234853341940780352/2832235053217244895688307872840207038615083217), upper := (99407566078886634576334584459028176247089950367337/112383086911660277460912056394299415292246502050560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint308_valid : endpoint308.Valid 8 := by
  constructor
  · norm_num [endpoint308, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint308, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint308PositiveFacts : PositiveEndpointFacts 8
    endpoint308 :=
  { valid := endpoint308_valid
    positive := by
      norm_num [endpoint308] }

noncomputable def endpoint309 : EndpointCache :=
  { input := (2449/1024), certificate := { exponent := 1, mantissa := (2449/2048) }, enclosure := { lower := (16289090167068831710659358685634146461170985460625640216000/18680936565501393957774482657238260496977325701850722704779), upper := (163397560796134924242401032998320243005541475291599199343588196075/187390417505947294935407444080953343824271239757137591926799446016) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint309_valid : endpoint309.Valid 8 := by
  constructor
  · norm_num [endpoint309, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint309, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint309PositiveFacts : PositiveEndpointFacts 8
    endpoint309 :=
  { valid := endpoint309_valid
    positive := by
      norm_num [endpoint309] }

noncomputable def endpoint310 : EndpointCache :=
  { input := (2505/1024), certificate := { exponent := 1, mantissa := (2505/2048) }, enclosure := { lower := (288705002246521019611075168918205641660022354560727950074070618432/322729680194808564181414176698873787628154523218659627856560937697), upper := (987417319714667309723626151314964504908211641642363015097293175828403259/1103787143015076458870705510578420173494308974131530912809895456673771520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint310_valid : endpoint310.Valid 8 := by
  constructor
  · norm_num [endpoint310, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint310, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint310PositiveFacts : PositiveEndpointFacts 8
    endpoint310 :=
  { valid := endpoint310_valid
    positive := by
      norm_num [endpoint310] }

noncomputable def endpoint311 : EndpointCache :=
  { input := (1979/1024), certificate := { exponent := 0, mantissa := (1979/1024) }, enclosure := { lower := (28790841517962097843500760667370023984985305892085120/43696961365851314194284475862801686527943606448861721), upper := (16669864531001970737624401748682708676793556766655451617095/25300490691443492802703060913732619012037601912626423474176) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint311_valid : endpoint311.Valid 8 := by
  constructor
  · norm_num [endpoint311, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint311, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint311PositiveFacts : PositiveEndpointFacts 8
    endpoint311 :=
  { valid := endpoint311_valid
    positive := by
      norm_num [endpoint311] }

noncomputable def endpoint312 : EndpointCache :=
  { input := (1007/512), certificate := { exponent := 0, mantissa := (1007/512) }, enclosure := { lower := (4650692047300109696996695656245481407895987899520/6875589825577649779213328482153631171125056520387), upper := (685092128662179997554763849663319363994149062546201605/1012841172751607709647407072040770792495240326002060288) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint312_valid : endpoint312.Valid 8 := by
  constructor
  · norm_num [endpoint312, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint312, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint312PositiveFacts : PositiveEndpointFacts 8
    endpoint312 :=
  { valid := endpoint312_valid
    positive := by
      norm_num [endpoint312] }

noncomputable def endpoint313 : EndpointCache :=
  { input := (1879/1024), certificate := { exponent := 0, mantissa := (1879/1024) }, enclosure := { lower := (5325310073800609923396985839117295227932610682421274240/8772828005792377845144768541292510057457847923944057407), upper := (20492815693319335418121818472153107258680019298240650416033455/33759526549266182084663337142453506863028830718138130161158144) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint313_valid : endpoint313.Valid 8 := by
  constructor
  · norm_num [endpoint313, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint313, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint313PositiveFacts : PositiveEndpointFacts 8
    endpoint313 :=
  { valid := endpoint313_valid
    positive := by
      norm_num [endpoint313] }

noncomputable def endpoint314 : EndpointCache :=
  { input := (957/512), certificate := { exponent := 0, mantissa := (957/512) }, enclosure := { lower := (138762700217830958012509175375661196929070645697920/221850377202769055129226689686009616404556121986457), upper := (4120697167766021845005128139985911033475369547233322945/6588068801413429861117515776915741568749698598509827072) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint314_valid : endpoint314.Valid 8 := by
  constructor
  · norm_num [endpoint314, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint314, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint314PositiveFacts : PositiveEndpointFacts 8
    endpoint314 :=
  { valid := endpoint314_valid
    positive := by
      norm_num [endpoint314] }

noncomputable def endpoint315 : EndpointCache :=
  { input := (7801/4096), certificate := { exponent := 0, mantissa := (7801/4096) }, enclosure := { lower := (671585077838564568647454469969967192151234175760316948256606080/1042443795842644222288912673396551435584150905619289827035004661), upper := (42918176654313621758427243031271154371536684067417573701828014026368485/66618196388810486399597017212243949559742146271117966874214984584896512) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint315_valid : endpoint315.Valid 8 := by
  constructor
  · norm_num [endpoint315, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint315, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint315PositiveFacts : PositiveEndpointFacts 8
    endpoint315 :=
  { valid := endpoint315_valid
    positive := by
      norm_num [endpoint315] }

noncomputable def endpoint316 : EndpointCache :=
  { input := (7891/4096), certificate := { exponent := 0, mantissa := (7891/4096) }, enclosure := { lower := (904507331841905389985084616714820813195307970580223318245580160/1379427793787730627867936219790546891793456172736979782311561113), upper := (4497702555076259990189530362074329243996034091378651605437678715580165/6859265399432417207220939042102165203506199731006232394654659343081472) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint316_valid : endpoint316.Valid 8 := by
  constructor
  · norm_num [endpoint316, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint316, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint316PositiveFacts : PositiveEndpointFacts 8
    endpoint316 :=
  { valid := endpoint316_valid
    positive := by
      norm_num [endpoint316] }

noncomputable def endpoint317 : EndpointCache :=
  { input := (1977/1024), certificate := { exponent := 0, mantissa := (1977/1024) }, enclosure := { lower := (427339123864071445308752329478904176453610974348148900736/649585800006462032210115829249786614648758845394552070045), upper := (576750563042675375811987928299277474902455597385478643995788847/876701782434321365455803046862048008301633698027540099398973440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint317_valid : endpoint317.Valid 8 := by
  constructor
  · norm_num [endpoint317, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint317, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint317PositiveFacts : PositiveEndpointFacts 8
    endpoint317 :=
  { valid := endpoint317_valid
    positive := by
      norm_num [endpoint317] }

noncomputable def endpoint318 : EndpointCache :=
  { input := (2001/1024), certificate := { exponent := 0, mantissa := (2001/1024) }, enclosure := { lower := (44582493994959108945570965640004509996189711140349427328/66547936099665088550651726659215143881738185882568359375), upper := (60900401036070379838038142696547383454780432180143576396759653/90905545479120105601607069044114433984756469726562500000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint318_valid : endpoint318.Valid 8 := by
  constructor
  · norm_num [endpoint318, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint318, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint318PositiveFacts : PositiveEndpointFacts 8
    endpoint318 :=
  { valid := endpoint318_valid
    positive := by
      norm_num [endpoint318] }

noncomputable def endpoint319 : EndpointCache :=
  { input := (503/256), certificate := { exponent := 0, mantissa := (503/256) }, enclosure := { lower := (1133405135461411845446908007082616728271001216/1678092658890615996059501773677242725903556895), upper := (291892629943990861518756637211607005402790861192911/432169271000053681161179848785742382658298428510720) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint319_valid : endpoint319.Valid 8 := by
  constructor
  · norm_num [endpoint319, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint319, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint319PositiveFacts : PositiveEndpointFacts 8
    endpoint319 :=
  { valid := endpoint319_valid
    positive := by
      norm_num [endpoint319] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
