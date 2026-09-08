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

noncomputable def endpoint128 : EndpointCache :=
  { input := (1605/1024), certificate := { exponent := 0, mantissa := (1605/1024) }, enclosure := { lower := (520780498106058635738624188253331534064855610482739072/1158816466188199693743557075945940725351182566053970165), upper := (114121755236789225573812232039978431795741737006653404971971/253938405134617328088188123394489666790556742794802806077440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint128_valid : endpoint128.Valid 8 := by
  constructor
  · norm_num [endpoint128, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint128, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint128PositiveFacts : PositiveEndpointFacts 8
    endpoint128 :=
  { valid := endpoint128_valid
    positive := by
      norm_num [endpoint128] }

noncomputable def endpoint129 : EndpointCache :=
  { input := (1635/1024), certificate := { exponent := 0, mantissa := (1635/1024) }, enclosure := { lower := (3807638713989695559454186698674466292612924812854082688/8137261990200174555604433416791121892000423327760280035), upper := (849986805454596853723307936741521969295042057446932182976917/1816497268596365366396688880497115722195038500302582832773120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint129_valid : endpoint129.Valid 8 := by
  constructor
  · norm_num [endpoint129, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint129, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint129PositiveFacts : PositiveEndpointFacts 8
    endpoint129 :=
  { valid := endpoint129_valid
    positive := by
      norm_num [endpoint129] }

noncomputable def endpoint130 : EndpointCache :=
  { input := (405/256), certificate := { exponent := 0, mantissa := (405/256) }, enclosure := { lower := (41515123501210523278807917039597675608231299456/90504147838822257822551582348152889274758800545), upper := (191301689102380481956223490114688914427845437384797/417043113241292964046317691460288513778088552911360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint130_valid : endpoint130.Valid 8 := by
  constructor
  · norm_num [endpoint130, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint130, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint130PositiveFacts : PositiveEndpointFacts 8
    endpoint130 :=
  { valid := endpoint130_valid
    positive := by
      norm_num [endpoint130] }

noncomputable def endpoint131 : EndpointCache :=
  { input := (413/256), certificate := { exponent := 0, mantissa := (413/256) }, enclosure := { lower := (17281855838232694057898885105243667166660674688/36134088429295034378959558460506410597390593235), upper := (522050301207223573945982568499157537476599457703869/1091538543272144398519610341974977651325975040442880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint131_valid : endpoint131.Valid 8 := by
  constructor
  · norm_num [endpoint131, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint131, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint131PositiveFacts : PositiveEndpointFacts 8
    endpoint131 :=
  { valid := endpoint131_valid
    positive := by
      norm_num [endpoint131] }

noncomputable def endpoint132 : EndpointCache :=
  { input := (419/256), certificate := { exponent := 0, mantissa := (419/256) }, enclosure := { lower := (20354420396281976361048391250643475795108027264/41312543013003438697312627919018268585205078125), upper := (4366593099381315332651608887889382493250336455423637/8862697227493601696857083442211151123046875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint132_valid : endpoint132.Valid 8 := by
  constructor
  · norm_num [endpoint132, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint132, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint132PositiveFacts : PositiveEndpointFacts 8
    endpoint132 :=
  { valid := endpoint132_valid
    positive := by
      norm_num [endpoint132] }

noncomputable def endpoint133 : EndpointCache :=
  { input := (107/64), certificate := { exponent := 0, mantissa := (107/64) }, enclosure := { lower := (24120387047036168269614571165721456512/46931776351263781962535614846813795765), upper := (330352821084411523262642873269197566337997/642777608906908757758887780941961746797440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint133_valid : endpoint133.Valid 8 := by
  constructor
  · norm_num [endpoint133, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint133, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint133PositiveFacts : PositiveEndpointFacts 8
    endpoint133 :=
  { valid := endpoint133_valid
    positive := by
      norm_num [endpoint133] }

noncomputable def endpoint134 : EndpointCache :=
  { input := (425/256), certificate := { exponent := 0, mantissa := (425/256) }, enclosure := { lower := (1839589826486058361725586175925672338470271104/3629014161240587609524049692846666829550142155), upper := (80058949265958919580881594397387342878522627031039/157934696297190372766486642632686940422022186585600) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint134_valid : endpoint134.Valid 8 := by
  constructor
  · norm_num [endpoint134, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint134, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint134PositiveFacts : PositiveEndpointFacts 8
    endpoint134 :=
  { valid := endpoint134_valid
    positive := by
      norm_num [endpoint134] }

noncomputable def endpoint135 : EndpointCache :=
  { input := (211/128), certificate := { exponent := 0, mantissa := (211/128) }, enclosure := { lower := (673505703072225337982974028827126267171712/1347475289196534579384631470587925286291485), upper := (36380084063471300789958083073333441718867643237/72785225221240011840040253515277372264320853760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint135_valid : endpoint135.Valid 8 := by
  constructor
  · norm_num [endpoint135, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint135, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint135PositiveFacts : PositiveEndpointFacts 8
    endpoint135 :=
  { valid := endpoint135_valid
    positive := by
      norm_num [endpoint135] }

noncomputable def endpoint136 : EndpointCache :=
  { input := (437/256), certificate := { exponent := 0, mantissa := (437/256) }, enclosure := { lower := (425783271045616962514307486842531567699438208/796220088455978146618448537356370246509638615), upper := (13609493177666500930984212501593261844260295636521/25449923924499196348142592791751957776436083182080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint136_valid : endpoint136.Valid 8 := by
  constructor
  · norm_num [endpoint136, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint136, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint136PositiveFacts : PositiveEndpointFacts 8
    endpoint136 :=
  { valid := endpoint136_valid
    positive := by
      norm_num [endpoint136] }

noncomputable def endpoint137 : EndpointCache :=
  { input := (217/128), certificate := { exponent := 0, mantissa := (217/128) }, enclosure := { lower := (925414604275495145858755764968531697784448/1753120477660333303813398994697113037109375), upper := (1049155757498390427179838658704700673431446719/1987537730101772157009019203130898437500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint137_valid : endpoint137.Valid 8 := by
  constructor
  · norm_num [endpoint137, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint137, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint137PositiveFacts : PositiveEndpointFacts 8
    endpoint137 :=
  { valid := endpoint137_valid
    positive := by
      norm_num [endpoint137] }

noncomputable def endpoint138 : EndpointCache :=
  { input := (221/128), certificate := { exponent := 0, mantissa := (221/128) }, enclosure := { lower := (379387885014643910882495994395176279634304/694681104638661826363347405964485846333745), upper := (1651096076704898716176120742017373130932470813/3023252167387456268333287910757442403244458240) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint138_valid : endpoint138.Valid 8 := by
  constructor
  · norm_num [endpoint138, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint138, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint138PositiveFacts : PositiveEndpointFacts 8
    endpoint138 :=
  { valid := endpoint138_valid
    positive := by
      norm_num [endpoint138] }

noncomputable def endpoint139 : EndpointCache :=
  { input := (111/64), certificate := { exponent := 0, mantissa := (111/64) }, enclosure := { lower := (15667245619054934851918934509822620544/28452424627247457392513751983642578125), upper := (10600010758429142180874568395123719172857/19250097576377708315849304199218750000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint139_valid : endpoint139.Valid 8 := by
  constructor
  · norm_num [endpoint139, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint139, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint139PositiveFacts : PositiveEndpointFacts 8
    endpoint139 :=
  { valid := endpoint139_valid
    positive := by
      norm_num [endpoint139] }

noncomputable def endpoint140 : EndpointCache :=
  { input := (67/64), certificate := { exponent := 0, mantissa := (67/64) }, enclosure := { lower := (13165259073560487987117095143999104/287391233662938832922177893017062255), upper := (112905261814854744977516208601282831719/2464667219893363431140597610514325898880) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint140_valid : endpoint140.Valid 8 := by
  constructor
  · norm_num [endpoint140, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint140, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint140PositiveFacts : PositiveEndpointFacts 8
    endpoint140 :=
  { valid := endpoint140_valid
    positive := by
      norm_num [endpoint140] }

noncomputable def endpoint141 : EndpointCache :=
  { input := (35/32), certificate := { exponent := 0, mantissa := (35/32) }, enclosure := { lower := (1103806790844908010365406083712/12317600725000030526914848215215), upper := (70643634614074112663404456400877/788326446400001953722550285773760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint141_valid : endpoint141.Valid 8 := by
  constructor
  · norm_num [endpoint141, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint141, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint141PositiveFacts : PositiveEndpointFacts 8
    endpoint141 :=
  { valid := endpoint141_valid
    positive := by
      norm_num [endpoint141] }

noncomputable def endpoint142 : EndpointCache :=
  { input := (311/256), certificate := { exponent := 0, mantissa := (311/256) }, enclosure := { lower := (1527523304367729631230994430047913252172160/7848930624183407409733042828608737521884177), upper := (34747227257297477097081057979254429670396824535/178542988735710332666658839383575213297808753152) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint142_valid : endpoint142.Valid 8 := by
  constructor
  · norm_num [endpoint142, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint142, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint142PositiveFacts : PositiveEndpointFacts 8
    endpoint142 :=
  { valid := endpoint142_valid
    positive := by
      norm_num [endpoint142] }

noncomputable def endpoint143 : EndpointCache :=
  { input := (329/256), certificate := { exponent := 0, mantissa := (329/256) }, enclosure := { lower := (93193698310265184823807735515996582654617728/371466775092726894514405153457135467529296875), upper := (2242613156138229241401671752973224967370263293837/8938976475831379989594645612792507890625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint143_valid : endpoint143.Valid 8 := by
  constructor
  · norm_num [endpoint143, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint143, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint143PositiveFacts : PositiveEndpointFacts 8
    endpoint143 :=
  { valid := endpoint143_valid
    positive := by
      norm_num [endpoint143] }

noncomputable def endpoint144 : EndpointCache :=
  { input := (167/128), certificate := { exponent := 0, mantissa := (167/128) }, enclosure := { lower := (1141860600078085959637672060709677832832/4293297357966233553961688724212646484375), upper := (48816824374538761036136666919283479604919079/183547048647772416898970116337539062500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint144_valid : endpoint144.Valid 8 := by
  constructor
  · norm_num [endpoint144, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint144, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint144PositiveFacts : PositiveEndpointFacts 8
    endpoint144 :=
  { valid := endpoint144_valid
    positive := by
      norm_num [endpoint144] }

noncomputable def endpoint145 : EndpointCache :=
  { input := (665/512), certificate := { exponent := 0, mantissa := (665/512) }, enclosure := { lower := (1371095194057725159306425043982373114570434123392/5243947551029993132642330028911768989225250958815), upper := (26676028095587280047935843512261456832220860992798021/102026243552839546388689173042507377454366482654704640) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint145_valid : endpoint145.Valid 8 := by
  constructor
  · norm_num [endpoint145, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint145, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint145PositiveFacts : PositiveEndpointFacts 8
    endpoint145 :=
  { valid := endpoint145_valid
    positive := by
      norm_num [endpoint145] }

noncomputable def endpoint146 : EndpointCache :=
  { input := (1349/1024), certificate := { exponent := 0, mantissa := (1349/1024) }, enclosure := { lower := (3875550167870502658212115656562785373442090640636800/14059828172722594072497392053347268496988292495436781), upper := (1529597711054961874534016510211295356590562174193675346675/5549116914835098888425759270024181819227342724050422511616) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint146_valid : endpoint146.Valid 8 := by
  constructor
  · norm_num [endpoint146, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint146, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint146PositiveFacts : PositiveEndpointFacts 8
    endpoint146 :=
  { valid := endpoint146_valid
    positive := by
      norm_num [endpoint146] }

noncomputable def endpoint147 : EndpointCache :=
  { input := (1343/1024), certificate := { exponent := 0, mantissa := (1343/1024) }, enclosure := { lower := (151837559962529471188092987621959596265185736195721344/559894911247476711686854564425651842277983406257241195), upper := (417623742524783666403517904062752089880120702207262078191851/1539970797169379786333072752688436068719271351507916646164480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint147_valid : endpoint147.Valid 8 := by
  constructor
  · norm_num [endpoint147, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint147, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint147PositiveFacts : PositiveEndpointFacts 8
    endpoint147 :=
  { valid := endpoint147_valid
    positive := by
      norm_num [endpoint147] }

noncomputable def endpoint148 : EndpointCache :=
  { input := (327/256), certificate := { exponent := 0, mantissa := (327/256) }, enclosure := { lower := (306240760908499693942681921814454627258819968/1251071778594125219219159789375367126975622665), upper := (17090684384781591332877837015622359531776389635859/69819813819780940234182869525460488622255549688320) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint148_valid : endpoint148.Valid 8 := by
  constructor
  · norm_num [endpoint148, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint148, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint148PositiveFacts : PositiveEndpointFacts 8
    endpoint148 :=
  { valid := endpoint148_valid
    positive := by
      norm_num [endpoint148] }

noncomputable def endpoint149 : EndpointCache :=
  { input := (333/256), certificate := { exponent := 0, mantissa := (333/256) }, enclosure := { lower := (54800347423442441631045228252436420956175232/208394037006179959594091372773534280252709165), upper := (1038137781589701257114652955330514252487654788813/3947816637045073154550466965821833405107322421760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint149_valid : endpoint149.Valid 8 := by
  constructor
  · norm_num [endpoint149, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint149, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint149PositiveFacts : PositiveEndpointFacts 8
    endpoint149 :=
  { valid := endpoint149_valid
    positive := by
      norm_num [endpoint149] }

noncomputable def endpoint150 : EndpointCache :=
  { input := (323/256), certificate := { exponent := 0, mantissa := (323/256) }, enclosure := { lower := (961789036705975435271492153408296114605935488/4137174054702228980618979513912726736910185485), upper := (159056823734287559464587249937461484211332101563893/684189296470435819898844356092831096843258834767360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint150_valid : endpoint150.Valid 8 := by
  constructor
  · norm_num [endpoint150, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint150, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint150PositiveFacts : PositiveEndpointFacts 8
    endpoint150 :=
  { valid := endpoint150_valid
    positive := by
      norm_num [endpoint150] }

noncomputable def endpoint151 : EndpointCache :=
  { input := (69/64), certificate := { exponent := 0, mantissa := (69/64) }, enclosure := { lower := (6977602791894686886455005187684480/92758381327225899219761551279213659), upper := (2934580374191136884817694653366928535/39011524946764721043282572423715001728) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint151_valid : endpoint151.Valid 8 := by
  constructor
  · norm_num [endpoint151, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint151, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint151PositiveFacts : PositiveEndpointFacts 8
    endpoint151 :=
  { valid := endpoint151_valid
    positive := by
      norm_num [endpoint151] }

noncomputable def endpoint152 : EndpointCache :=
  { input := (1289/1024), certificate := { exponent := 0, mantissa := (1289/1024) }, enclosure := { lower := (200540076081521269024005696663587573896063934631877760/871344358595077454949688709742768480486992637794004771), upper := (529400131725478186191175674938209880540426777370470450968595/2300237574613104311152944633566061714120158228718534962829312) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint152_valid : endpoint152.Valid 8 := by
  constructor
  · norm_num [endpoint152, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint152, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint152PositiveFacts : PositiveEndpointFacts 8
    endpoint152 :=
  { valid := endpoint152_valid
    positive := by
      norm_num [endpoint152] }

noncomputable def endpoint153 : EndpointCache :=
  { input := (1309/1024), certificate := { exponent := 0, mantissa := (1309/1024) }, enclosure := { lower := (81150223755197780106339097083741762402075957656081280/330487592485767141130640328200908605627269515012600957), upper := (2825326190260972931678973700565090274027725446936010610105/11506256019984468785604373666642834013519015434678714918912) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint153_valid : endpoint153.Valid 8 := by
  constructor
  · norm_num [endpoint153, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint153, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint153PositiveFacts : PositiveEndpointFacts 8
    endpoint153 :=
  { valid := endpoint153_valid
    positive := by
      norm_num [endpoint153] }

noncomputable def endpoint154 : EndpointCache :=
  { input := (161/128), certificate := { exponent := 0, mantissa := (161/128) }, enclosure := { lower := (855112820136295782210389507383663899264/3728026905245718328232070468100459576295), upper := (5034904284962513808433030556663806207470177/21950622418086789516630430916175505985224960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint154_valid : endpoint154.Valid 8 := by
  constructor
  · norm_num [endpoint154, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint154, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint154PositiveFacts : PositiveEndpointFacts 8
    endpoint154 :=
  { valid := endpoint154_valid
    positive := by
      norm_num [endpoint154] }

noncomputable def endpoint155 : EndpointCache :=
  { input := (367/256), certificate := { exponent := 0, mantissa := (367/256) }, enclosure := { lower := (212888227026015468461612557218168803551514496/591053429612742804498954742902649109302524005), upper := (5714649915876937214096742721967259356445138428307/15865900519707546276653084572911339747768781519360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint155_valid : endpoint155.Valid 8 := by
  constructor
  · norm_num [endpoint155, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint155, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint155PositiveFacts : PositiveEndpointFacts 8
    endpoint155 :=
  { valid := endpoint155_valid
    positive := by
      norm_num [endpoint155] }

noncomputable def endpoint156 : EndpointCache :=
  { input := (183/128), certificate := { exponent := 0, mantissa := (183/128) }, enclosure := { lower := (7209616988906626918973101348020507885440/20169249444045895473820634166421672173669), upper := (112585378898871161722589336392481311441765415/314962999318220703719183023142840832664015104) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint156_valid : endpoint156.Valid 8 := by
  constructor
  · norm_num [endpoint156, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint156, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint156PositiveFacts : PositiveEndpointFacts 8
    endpoint156 :=
  { valid := endpoint156_valid
    positive := by
      norm_num [endpoint156] }

noncomputable def endpoint157 : EndpointCache :=
  { input := (363/256), certificate := { exponent := 0, mantissa := (363/256) }, enclosure := { lower := (11806254405258306825858675053625092605938792064/33806976097922057980097119054651396222322383455), upper := (66492824810457901870865729958006538866475613762503/190400889383497030543906974515796663524119663618560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint157_valid : endpoint157.Valid 8 := by
  constructor
  · norm_num [endpoint157, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint157, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint157PositiveFacts : PositiveEndpointFacts 8
    endpoint157 :=
  { valid := endpoint157_valid
    positive := by
      norm_num [endpoint157] }

noncomputable def endpoint158 : EndpointCache :=
  { input := (733/512), certificate := { exponent := 0, mantissa := (733/512) }, enclosure := { lower := (11091753283984215928741816923674233993672796223104/30911654859978870238377330216784561694183349609375), upper := (8325381280940545750427991689943258462386927333990270423/23202040844661260169964117042076757731160468750000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint158_valid : endpoint158.Valid 8 := by
  constructor
  · norm_num [endpoint158, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint158, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint158PositiveFacts : PositiveEndpointFacts 8
    endpoint158 :=
  { valid := endpoint158_valid
    positive := by
      norm_num [endpoint158] }

noncomputable def endpoint159 : EndpointCache :=
  { input := (5941/4096), certificate := { exponent := 0, mantissa := (5941/4096) }, enclosure := { lower := (393441431280909118240751951175432894433563487395815104019468160/1058017715788311583034667840353537833089806486788493489198931493), upper := (1472943997711876940628000355133132798807603030082193933670595988831665/3960947475376196759116539519316515141402964496075501769227564583329792) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint159_valid : endpoint159.Valid 8 := by
  constructor
  · norm_num [endpoint159, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint159, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint159PositiveFacts : PositiveEndpointFacts 8
    endpoint159 :=
  { valid := endpoint159_valid
    positive := by
      norm_num [endpoint159] }

noncomputable def endpoint160 : EndpointCache :=
  { input := (187/128), certificate := { exponent := 0, mantissa := (187/128) }, enclosure := { lower := (24255743329902632731802363780557684724864/63986094542483735458728829651336669921875), upper := (15080142138854899426410328740374181175562119/39781069064127030959483980948945312500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint160_valid : endpoint160.Valid 8 := by
  constructor
  · norm_num [endpoint160, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint160, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint160PositiveFacts : PositiveEndpointFacts 8
    endpoint160 :=
  { valid := endpoint160_valid
    positive := by
      norm_num [endpoint160] }

noncomputable def endpoint161 : EndpointCache :=
  { input := (371/256), certificate := { exponent := 0, mantissa := (371/256) }, enclosure := { lower := (92167644025441976465465451194972255333599360/248413823563819971933872753516920753096042539), upper := (2501061188278590366328651684636988996495491686085/6740957516227818758397571039435161556014210338304) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint161_valid : endpoint161.Valid 8 := by
  constructor
  · norm_num [endpoint161, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint161, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint161PositiveFacts : PositiveEndpointFacts 8
    endpoint161 :=
  { valid := endpoint161_valid
    positive := by
      norm_num [endpoint161] }

noncomputable def endpoint162 : EndpointCache :=
  { input := (181/128), certificate := { exponent := 0, mantissa := (181/128) }, enclosure := { lower := (116295821777124714885340585260044537002112/335662270491066925828567411303139139272235), upper := (5388683197867935504455880423722407066333551827/15553246965474077075192499570142255157318280960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint162_valid : endpoint162.Valid 8 := by
  constructor
  · norm_num [endpoint162, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint162, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint162PositiveFacts : PositiveEndpointFacts 8
    endpoint162 :=
  { valid := endpoint162_valid
    positive := by
      norm_num [endpoint162] }

noncomputable def endpoint163 : EndpointCache :=
  { input := (185/128), certificate := { exponent := 0, mantissa := (185/128) }, enclosure := { lower := (49980546925602699872485221740559349692288/135696655883382977964683156579708889991285), upper := (473415740480017218982349524886966293972176993/1285318724527403567281478859123002605997451520) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint163_valid : endpoint163.Valid 8 := by
  constructor
  · norm_num [endpoint163, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint163, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint163PositiveFacts : PositiveEndpointFacts 8
    endpoint163 :=
  { valid := endpoint163_valid
    positive := by
      norm_num [endpoint163] }

noncomputable def endpoint164 : EndpointCache :=
  { input := (387/256), certificate := { exponent := 0, mantissa := (387/256) }, enclosure := { lower := (24718445530413566867323885680408284782308754048/59815148478654197077449529823976632686724803815), upper := (544201296802517009111892360451646292589375334478823/1316890308906050802857128848604669545230933280791040) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint164_valid : endpoint164.Valid 8 := by
  constructor
  · norm_num [endpoint164, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint164, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint164PositiveFacts : PositiveEndpointFacts 8
    endpoint164 :=
  { valid := endpoint164_valid
    positive := by
      norm_num [endpoint164] }

noncomputable def endpoint165 : EndpointCache :=
  { input := (399/256), certificate := { exponent := 0, mantissa := (399/256) }, enclosure := { lower := (244963662697462704106232280635621289921206144/551988530291886655644685126277376251220703125), upper := (2383006510786502090871441880653396708267387098977/5369744422679473386111496908426316171875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint165_valid : endpoint165.Valid 8 := by
  constructor
  · norm_num [endpoint165, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint165, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint165PositiveFacts : PositiveEndpointFacts 8
    endpoint165 :=
  { valid := endpoint165_valid
    positive := by
      norm_num [endpoint165] }

noncomputable def endpoint166 : EndpointCache :=
  { input := (207/128), certificate := { exponent := 0, mantissa := (207/128) }, enclosure := { lower := (1626231823663934229634699471872246744354944/3383130081939705650092579160673065185546875), upper := (9575252978643293444382803677336867767801160067/19919869922460986867745106098043007812500000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint166_valid : endpoint166.Valid 8 := by
  constructor
  · norm_num [endpoint166, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint166, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint166PositiveFacts : PositiveEndpointFacts 8
    endpoint166 :=
  { valid := endpoint166_valid
    positive := by
      norm_num [endpoint166] }

noncomputable def endpoint167 : EndpointCache :=
  { input := (209/128), certificate := { exponent := 0, mantissa := (209/128) }, enclosure := { lower := (201519937880430989505654495877509266047872/411010195298220845888467314709512906659965), upper := (980192977976964750152384015570270098242300663/1999153589930546194401505018747070777994069760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint167_valid : endpoint167.Valid 8 := by
  constructor
  · norm_num [endpoint167, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint167, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint167PositiveFacts : PositiveEndpointFacts 8
    endpoint167 :=
  { valid := endpoint167_valid
    positive := by
      norm_num [endpoint167] }

noncomputable def endpoint168 : EndpointCache :=
  { input := (203/128), certificate := { exponent := 0, mantissa := (203/128) }, enclosure := { lower := (28954789633988664135716870749719082934400/62784723229415786917176171449133321775451), upper := (214960358253481076493607939552043164331938725/466113785255182802073115896838365780860948224) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint168_valid : endpoint168.Valid 8 := by
  constructor
  · norm_num [endpoint168, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint168, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint168PositiveFacts : PositiveEndpointFacts 8
    endpoint168 :=
  { valid := endpoint168_valid
    positive := by
      norm_num [endpoint168] }

noncomputable def endpoint169 : EndpointCache :=
  { input := (1617/1024), certificate := { exponent := 0, mantissa := (1617/1024) }, enclosure := { lower := (43646758301053391712370895575633401180916512739915198336/95537222110005389606730507556538112832587098325985587045), upper := (625719927030938790740976626215565250001892406905647582628531/1369621616169037265402088556330530385567968641601329375877120) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint169_valid : endpoint169.Valid 8 := by
  constructor
  · norm_num [endpoint169, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint169, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint169PositiveFacts : PositiveEndpointFacts 8
    endpoint169 :=
  { valid := endpoint169_valid
    positive := by
      norm_num [endpoint169] }

noncomputable def endpoint170 : EndpointCache :=
  { input := (819/512), certificate := { exponent := 0, mantissa := (819/512) }, enclosure := { lower := (140216871119759638464789137318109208650720412925824/298486530690496998525187239495884732258807371051845), upper := (6837241716009089877346705360666883551176545792495491/14554771782241377451894844440180284087286607045575680) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint170_valid : endpoint170.Valid 8 := by
  constructor
  · norm_num [endpoint170, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint170, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint170PositiveFacts : PositiveEndpointFacts 8
    endpoint170 :=
  { valid := endpoint170_valid
    positive := by
      norm_num [endpoint170] }

noncomputable def endpoint171 : EndpointCache :=
  { input := (421/256), certificate := { exponent := 0, mantissa := (421/256) }, enclosure := { lower := (130204370668490034481953490544263211540219520/261740798262078185416256228462979126217299263), upper := (28065812510866140005177281218140930361899575709415/56418752546987477022844862557652076614391290738176) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint171_valid : endpoint171.Valid 8 := by
  constructor
  · norm_num [endpoint171, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint171, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint171PositiveFacts : PositiveEndpointFacts 8
    endpoint171 :=
  { valid := endpoint171_valid
    positive := by
      norm_num [endpoint171] }

noncomputable def endpoint172 : EndpointCache :=
  { input := (6663/4096), certificate := { exponent := 0, mantissa := (6663/4096) }, enclosure := { lower := (9381291392996908593669581528590298311140443920078006123559853952/19280893863337092939810309255665261062222856081000720384837522565), upper := (24383895477377280762471934999672225857716189955341919054589460964400097/50114987470814861510151252093024601022694503401650585570420019336765440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint172_valid : endpoint172.Valid 8 := by
  constructor
  · norm_num [endpoint172, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint172, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint172PositiveFacts : PositiveEndpointFacts 8
    endpoint172 :=
  { valid := endpoint172_valid
    positive := by
      norm_num [endpoint172] }

noncomputable def endpoint173 : EndpointCache :=
  { input := (3371/2048), certificate := { exponent := 0, mantissa := (3371/2048) }, enclosure := { lower := (36360014488322347722995434550067718827978262307944175167872/72961424905133600897062943397090024855125014860259181498785), upper := (502045117892525685063653744963615789431411771104375472565360718297/1007423337902921189883900650256754580630021837184752438609527746560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint173_valid : endpoint173.Valid 8 := by
  constructor
  · norm_num [endpoint173, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint173, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint173PositiveFacts : PositiveEndpointFacts 8
    endpoint173 :=
  { valid := endpoint173_valid
    positive := by
      norm_num [endpoint173] }

noncomputable def endpoint174 : EndpointCache :=
  { input := (423/256), certificate := { exponent := 0, mantissa := (423/256) }, enclosure := { lower := (9715548415482435092673569315787283211183124352/19346177382705819980171780865757055703027110565), upper := (11133093195898561065767111910433050107211983498873/22168876787496802476326368321598942306554494696960) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint174_valid : endpoint174.Valid 8 := by
  constructor
  · norm_num [endpoint174, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint174, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint174PositiveFacts : PositiveEndpointFacts 8
    endpoint174 :=
  { valid := endpoint174_valid
    positive := by
      norm_num [endpoint174] }

noncomputable def endpoint175 : EndpointCache :=
  { input := (219/128), certificate := { exponent := 0, mantissa := (219/128) }, enclosure := { lower := (33849724659991389597179176181293261996928/63030001984107394058219246234303420292285), upper := (632583654777956954544336186169307427659407079/1177904677078998980160001273626662318422222080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint175_valid : endpoint175.Valid 8 := by
  constructor
  · norm_num [endpoint175, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint175, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint175PositiveFacts : PositiveEndpointFacts 8
    endpoint175 :=
  { valid := endpoint175_valid
    positive := by
      norm_num [endpoint175] }

noncomputable def endpoint176 : EndpointCache :=
  { input := (873/512), certificate := { exponent := 0, mantissa := (873/512) }, enclosure := { lower := (3181397310502953085580078376632253612182939760630656/5962016755955742430213315693157606649938507080078125), upper := (35111314689773410871106090553550827379311411928236329197/65799466703952442678692024574439861480565781250000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint176_valid : endpoint176.Valid 8 := by
  constructor
  · norm_num [endpoint176, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint176, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint176PositiveFacts : PositiveEndpointFacts 8
    endpoint176 :=
  { valid := endpoint176_valid
    positive := by
      norm_num [endpoint176] }

noncomputable def endpoint177 : EndpointCache :=
  { input := (1777/1024), certificate := { exponent := 0, mantissa := (1777/1024) }, enclosure := { lower := (14138971524427886295140275847392256947819210971373970304/25650788168782900049351801671990879958681772781126215005), upper := (51455902553228472039549077482806263487106727110188051847695549/93350810779498933018005814417669721470110740955261509762836480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint177_valid : endpoint177.Valid 8 := by
  constructor
  · norm_num [endpoint177, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint177, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint177PositiveFacts : PositiveEndpointFacts 8
    endpoint177 :=
  { valid := endpoint177_valid
    positive := by
      norm_num [endpoint177] }

noncomputable def endpoint178 : EndpointCache :=
  { input := (449/256), certificate := { exponent := 0, mantissa := (449/256) }, enclosure := { lower := (44563465266933989913982599770212904603097268864/79316235103509229614552308549323013763427734375), upper := (10244605914024805049428501991869560031595044378545127/18233850655475529777630201107786768988046875000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint178_valid : endpoint178.Valid 8 := by
  constructor
  · norm_num [endpoint178, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint178, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint178PositiveFacts : PositiveEndpointFacts 8
    endpoint178 :=
  { valid := endpoint178_valid
    positive := by
      norm_num [endpoint178] }

noncomputable def endpoint179 : EndpointCache :=
  { input := (441/256), certificate := { exponent := 0, mantissa := (441/256) }, enclosure := { lower := (21810283492093674076020392947456170454019419520/40102205521140418656465075365592816059361617337), upper := (78168056085466718258729173302010100828683871044055/143726304587767260464770830110284652756752036535808) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint179_valid : endpoint179.Valid 8 := by
  constructor
  · norm_num [endpoint179, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint179, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint179PositiveFacts : PositiveEndpointFacts 8
    endpoint179 :=
  { valid := endpoint179_valid
    positive := by
      norm_num [endpoint179] }

noncomputable def endpoint180 : EndpointCache :=
  { input := (443/256), certificate := { exponent := 0, mantissa := (443/256) }, enclosure := { lower := (3478417088682621084397345363712067673798971008/6342935388897104318743356809840824286010081135), upper := (788960650957379554366375460072714746714282744752983/1438679233168085613160093218180856401255662562716160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint180_valid : endpoint180.Valid 8 := by
  constructor
  · norm_num [endpoint180, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint180, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint180PositiveFacts : PositiveEndpointFacts 8
    endpoint180 :=
  { valid := endpoint180_valid
    positive := by
      norm_num [endpoint180] }

noncomputable def endpoint181 : EndpointCache :=
  { input := (1807/1024), certificate := { exponent := 0, mantissa := (1807/1024) }, enclosure := { lower := (17092805928017904861652877481794515799148275885886463104/30095538757976971291762679870062257203249605477112814755), upper := (4865843255158137991627505133286103898262988552186691589849743/8567357209310820371568665603970362882563471690380659201935360) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint181_valid : endpoint181.Valid 8 := by
  constructor
  · norm_num [endpoint181, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint181, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint181PositiveFacts : PositiveEndpointFacts 8
    endpoint181 :=
  { valid := endpoint181_valid
    positive := by
      norm_num [endpoint181] }

noncomputable def endpoint182 : EndpointCache :=
  { input := (907/512), certificate := { exponent := 0, mantissa := (907/512) }, enclosure := { lower := (29727354915335200708258833136251099651902051976320/51987457567943376477691099186916506111806666228627), upper := (27609816007877610476091083949227139281116758387628320635/48284286990463633884432206809634069548450453779829441536) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint182_valid : endpoint182.Valid 8 := by
  constructor
  · norm_num [endpoint182, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint182, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint182PositiveFacts : PositiveEndpointFacts 8
    endpoint182 :=
  { valid := endpoint182_valid
    positive := by
      norm_num [endpoint182] }

noncomputable def endpoint183 : EndpointCache :=
  { input := (457/256), certificate := { exponent := 0, mantissa := (457/256) }, enclosure := { lower := (18147003636128823339042373755073698826405375872/31314611610427836497411735120884153452568661285), upper := (4246108505936605277822540665045823228304729912256053/7327118083054346895010387430524957761445825642109440) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint183_valid : endpoint183.Valid 8 := by
  constructor
  · norm_num [endpoint183, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint183, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint183PositiveFacts : PositiveEndpointFacts 8
    endpoint183 :=
  { valid := endpoint183_valid
    positive := by
      norm_num [endpoint183] }

noncomputable def endpoint184 : EndpointCache :=
  { input := (459/256), certificate := { exponent := 0, mantissa := (459/256) }, enclosure := { lower := (171443632185007500909009469334733169691288192/293631836095755578835672597067300872802734375), upper := (4476736132056085904119119748100465017478427627319/7667314504132369674557082854621360390625000000000) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint184_valid : endpoint184.Valid 8 := by
  constructor
  · norm_num [endpoint184, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint184, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint184PositiveFacts : PositiveEndpointFacts 8
    endpoint184 :=
  { valid := endpoint184_valid
    positive := by
      norm_num [endpoint184] }

noncomputable def endpoint185 : EndpointCache :=
  { input := (231/128), certificate := { exponent := 0, mantissa := (231/128) }, enclosure := { lower := (5638978443568222173431538017858373531614336/9551318336383391080706040805123483800437955), upper := (1443578484776517759328388462350325968800013301/2445137494114148116660746446111611852912116480) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint185_valid : endpoint185.Valid 8 := by
  constructor
  · norm_num [endpoint185, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint185, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint185PositiveFacts : PositiveEndpointFacts 8
    endpoint185 :=
  { valid := endpoint185_valid
    positive := by
      norm_num [endpoint185] }

noncomputable def endpoint186 : EndpointCache :=
  { input := (465/256), certificate := { exponent := 0, mantissa := (465/256) }, enclosure := { lower := (2582600811132100622109893993139612002618707328/4326979492367485677543173689084147647375438585), upper := (5855862883188637987655817925488336763472379380401/9811116928979533239137893256163370208448994460160) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint186_valid : endpoint186.Valid 8 := by
  constructor
  · norm_num [endpoint186, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint186, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint186PositiveFacts : PositiveEndpointFacts 8
    endpoint186 :=
  { valid := endpoint186_valid
    positive := by
      norm_num [endpoint186] }

noncomputable def endpoint187 : EndpointCache :=
  { input := (461/256), certificate := { exponent := 0, mantissa := (461/256) }, enclosure := { lower := (12019402970853436450404258335950272510405345920/20433495533195238701007076430651238671590539879), upper := (2836963728005708020593748453398294123216857645298815/4822958817691138581076102264079473166132858308720128) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint187_valid : endpoint187.Valid 8 := by
  constructor
  · norm_num [endpoint187, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint187, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint187PositiveFacts : PositiveEndpointFacts 8
    endpoint187 :=
  { valid := endpoint187_valid
    positive := by
      norm_num [endpoint187] }

noncomputable def endpoint188 : EndpointCache :=
  { input := (467/256), certificate := { exponent := 0, mantissa := (467/256) }, enclosure := { lower := (69595948367204684729706130193028555253376492416/115771003018167813929948677193591096626120456605), upper := (16640669687294160202616850171223439700350096451417829/27681309905655996981906448511696405567691905656081920) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint188_valid : endpoint188.Valid 8 := by
  constructor
  · norm_num [endpoint188, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint188, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint188PositiveFacts : PositiveEndpointFacts 8
    endpoint188 :=
  { valid := endpoint188_valid
    positive := by
      norm_num [endpoint188] }

noncomputable def endpoint189 : EndpointCache :=
  { input := (235/128), certificate := { exponent := 0, mantissa := (235/128) }, enclosure := { lower := (207643243908812365768106269743577469482624/341768495743911671223133321014049073117055), upper := (2498363519334395910856265835558186078482303579/4112158540790745228156740118441038447744405760) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint189_valid : endpoint189.Valid 8 := by
  constructor
  · norm_num [endpoint189, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint189, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint189PositiveFacts : PositiveEndpointFacts 8
    endpoint189 :=
  { valid := endpoint189_valid
    positive := by
      norm_num [endpoint189] }

noncomputable def endpoint190 : EndpointCache :=
  { input := (189/128), certificate := { exponent := 0, mantissa := (189/128) }, enclosure := { lower := (575817153017135744096247685807022008331648/1477527335771017303201077761936487747268185), upper := (442227573518763176593475465719713805032699679/1134740993872141288858427721167222589901966080) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint190_valid : endpoint190.Valid 8 := by
  constructor
  · norm_num [endpoint190, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint190, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint190PositiveFacts : PositiveEndpointFacts 8
    endpoint190 :=
  { valid := endpoint190_valid
    positive := by
      norm_num [endpoint190] }

noncomputable def endpoint191 : EndpointCache :=
  { input := (383/256), certificate := { exponent := 0, mantissa := (383/256) }, enclosure := { lower := (7314585326270211098640174846940669660963708288/18156753975403818602669323863587646960343808985), upper := (1434360924149016820992400325769622833537609034715353/3560466827560787212709043732354083218335579566722560) } }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem endpoint191_valid : endpoint191.Valid 8 := by
  constructor
  · norm_num [endpoint191, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.check]
  · norm_num [endpoint191, EndpointCache.Valid,
      RationalEnclosure.LogRangeCertificate.enclosure,
      RationalEnclosure.logScaledMantissaEnclosure,
      RationalEnclosure.logTwoEnclosure,
      RationalEnclosure.logMantissaEnclosure,
      RationalEnclosure.halfLogRatioEnclosure,
      RationalEnclosure.atanhPartial, RationalEnclosure.atanhTail,
      RationalEnclosure.logRatioCoordinate, RationalEnclosure.add,
      RationalEnclosure.scale, RationalEnclosure.mul,
      RationalEnclosure.point, RationalEnclosure.center,
      RationalEnclosure.radius]

theorem endpoint191PositiveFacts : PositiveEndpointFacts 8
    endpoint191 :=
  { valid := endpoint191_valid
    positive := by
      norm_num [endpoint191] }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
