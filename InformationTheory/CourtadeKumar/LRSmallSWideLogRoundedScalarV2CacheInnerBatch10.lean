import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7

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

noncomputable def innerPair640Data : WideLogData :=
  { lower := endpoint377
    upper := endpoint378 }

noncomputable def innerPair640Input : RationalEnclosure :=
  { lower := (6596167/8388608), upper := (13400013/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair640Input_eq :
    innerPair640Input = outerEnclosure 24 innerPair640Data.output := by
  rfl'

theorem innerPair640RoundedFacts :
    InnerPairRoundedFacts innerPair640Data innerPair640Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair640Input_eq }

noncomputable def innerPair641Data : WideLogData :=
  { lower := endpoint381
    upper := endpoint382 }

noncomputable def innerPair641Input : RationalEnclosure :=
  { lower := (13457043/16777216), upper := (6823485/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair641Input_eq :
    innerPair641Input = outerEnclosure 24 innerPair641Data.output := by
  rfl'

theorem innerPair641RoundedFacts :
    InnerPairRoundedFacts innerPair641Data innerPair641Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair641Input_eq }

noncomputable def innerPair642Data : WideLogData :=
  { lower := endpoint383
    upper := endpoint384 }

noncomputable def innerPair642Input : RationalEnclosure :=
  { lower := (13561403/16777216), upper := (13757377/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair642Input_eq :
    innerPair642Input = outerEnclosure 24 innerPair642Data.output := by
  rfl'

theorem innerPair642RoundedFacts :
    InnerPairRoundedFacts innerPair642Data innerPair642Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair642Input_eq }

noncomputable def innerPair643Data : WideLogData :=
  { lower := endpoint385
    upper := endpoint386 }

noncomputable def innerPair643Input : RationalEnclosure :=
  { lower := (13643337/16777216), upper := (6916487/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair643Input_eq :
    innerPair643Input = outerEnclosure 24 innerPair643Data.output := by
  rfl'

theorem innerPair643RoundedFacts :
    InnerPairRoundedFacts innerPair643Data innerPair643Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair643Input_eq }

noncomputable def innerPair644Data : WideLogData :=
  { lower := endpoint387
    upper := endpoint388 }

noncomputable def innerPair644Input : RationalEnclosure :=
  { lower := (1707913/2097152), upper := (13865269/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair644Input_eq :
    innerPair644Input = outerEnclosure 24 innerPair644Data.output := by
  rfl'

theorem innerPair644RoundedFacts :
    InnerPairRoundedFacts innerPair644Data innerPair644Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair644Input_eq }

noncomputable def innerPair645Data : WideLogData :=
  { lower := endpoint388
    upper := endpoint397 }

noncomputable def innerPair645Input : RationalEnclosure :=
  { lower := (3466317/4194304), upper := (14093147/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair645Input_eq :
    innerPair645Input = outerEnclosure 24 innerPair645Data.output := by
  rfl'

theorem innerPair645RoundedFacts :
    InnerPairRoundedFacts innerPair645Data innerPair645Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair645Input_eq }

noncomputable def innerPair646Data : WideLogData :=
  { lower := endpoint389
    upper := endpoint390 }

noncomputable def innerPair646Input : RationalEnclosure :=
  { lower := (6889505/8388608), upper := (13979595/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair646Input_eq :
    innerPair646Input = outerEnclosure 24 innerPair646Data.output := by
  rfl'

theorem innerPair646RoundedFacts :
    InnerPairRoundedFacts innerPair646Data innerPair646Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair646Input_eq }

noncomputable def innerPair647Data : WideLogData :=
  { lower := endpoint389
    upper := endpoint397 }

noncomputable def innerPair647Input : RationalEnclosure :=
  { lower := (6889505/8388608), upper := (14093147/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair647Input_eq :
    innerPair647Input = outerEnclosure 24 innerPair647Data.output := by
  rfl'

theorem innerPair647RoundedFacts :
    InnerPairRoundedFacts innerPair647Data innerPair647Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair647Input_eq }

noncomputable def innerPair648Data : WideLogData :=
  { lower := endpoint390
    upper := endpoint396 }

noncomputable def innerPair648Input : RationalEnclosure :=
  { lower := (6989797/8388608), upper := (14205935/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair648Input_eq :
    innerPair648Input = outerEnclosure 24 innerPair648Data.output := by
  rfl'

theorem innerPair648RoundedFacts :
    InnerPairRoundedFacts innerPair648Data innerPair648Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair648Input_eq }

noncomputable def innerPair649Data : WideLogData :=
  { lower := endpoint391
    upper := endpoint392 }

noncomputable def innerPair649Input : RationalEnclosure :=
  { lower := (13831177/16777216), upper := (14020491/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair649Input_eq :
    innerPair649Input = outerEnclosure 24 innerPair649Data.output := by
  rfl'

theorem innerPair649RoundedFacts :
    InnerPairRoundedFacts innerPair649Data innerPair649Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair649Input_eq }

noncomputable def innerPair650Data : WideLogData :=
  { lower := endpoint393
    upper := endpoint394 }

noncomputable def innerPair650Input : RationalEnclosure :=
  { lower := (435079/524288), upper := (3537409/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair650Input_eq :
    innerPair650Input = outerEnclosure 24 innerPair650Data.output := by
  rfl'

theorem innerPair650RoundedFacts :
    InnerPairRoundedFacts innerPair650Data innerPair650Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair650Input_eq }

noncomputable def innerPair651Data : WideLogData :=
  { lower := endpoint394
    upper := endpoint409 }

noncomputable def innerPair651Input : RationalEnclosure :=
  { lower := (7074817/8388608), upper := (14704305/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair651Input_eq :
    innerPair651Input = outerEnclosure 24 innerPair651Data.output := by
  rfl'

theorem innerPair651RoundedFacts :
    InnerPairRoundedFacts innerPair651Data innerPair651Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair651Input_eq }

noncomputable def innerPair652Data : WideLogData :=
  { lower := endpoint394
    upper := endpoint418 }

noncomputable def innerPair652Input : RationalEnclosure :=
  { lower := (7074817/8388608), upper := (7228485/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair652Input_eq :
    innerPair652Input = outerEnclosure 24 innerPair652Data.output := by
  rfl'

theorem innerPair652RoundedFacts :
    InnerPairRoundedFacts innerPair652Data innerPair652Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair652Input_eq }

noncomputable def innerPair653Data : WideLogData :=
  { lower := endpoint395
    upper := endpoint396 }

noncomputable def innerPair653Input : RationalEnclosure :=
  { lower := (7004027/8388608), upper := (14205935/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair653Input_eq :
    innerPair653Input = outerEnclosure 24 innerPair653Data.output := by
  rfl'

theorem innerPair653RoundedFacts :
    InnerPairRoundedFacts innerPair653Data innerPair653Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair653Input_eq }

noncomputable def innerPair654Data : WideLogData :=
  { lower := endpoint398
    upper := endpoint399 }

noncomputable def innerPair654Input : RationalEnclosure :=
  { lower := (7060707/8388608), upper := (7158985/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair654Input_eq :
    innerPair654Input = outerEnclosure 24 innerPair654Data.output := by
  rfl'

theorem innerPair654RoundedFacts :
    InnerPairRoundedFacts innerPair654Data innerPair654Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair654Input_eq }

noncomputable def innerPair655Data : WideLogData :=
  { lower := endpoint399
    upper := endpoint401 }

noncomputable def innerPair655Input : RationalEnclosure :=
  { lower := (14317969/16777216), upper := (14539821/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair655Input_eq :
    innerPair655Input = outerEnclosure 24 innerPair655Data.output := by
  rfl'

theorem innerPair655RoundedFacts :
    InnerPairRoundedFacts innerPair655Data innerPair655Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair655Input_eq }

noncomputable def innerPair656Data : WideLogData :=
  { lower := endpoint400
    upper := endpoint303 }

noncomputable def innerPair656Input : RationalEnclosure :=
  { lower := (14234013/16777216), upper := (7214631/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair656Input_eq :
    innerPair656Input = outerEnclosure 24 innerPair656Data.output := by
  rfl'

theorem innerPair656RoundedFacts :
    InnerPairRoundedFacts innerPair656Data innerPair656Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair656Input_eq }

noncomputable def innerPair657Data : WideLogData :=
  { lower := endpoint403
    upper := endpoint414 }

noncomputable def innerPair657Input : RationalEnclosure :=
  { lower := (940953/1048576), upper := (7633811/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair657Input_eq :
    innerPair657Input = outerEnclosure 24 innerPair657Data.output := by
  rfl'

theorem innerPair657RoundedFacts :
    InnerPairRoundedFacts innerPair657Data innerPair657Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair657Input_eq }

noncomputable def innerPair658Data : WideLogData :=
  { lower := endpoint403
    upper := endpoint419 }

noncomputable def innerPair658Input : RationalEnclosure :=
  { lower := (940953/1048576), upper := (3869335/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair658Input_eq :
    innerPair658Input = outerEnclosure 24 innerPair658Data.output := by
  rfl'

theorem innerPair658RoundedFacts :
    InnerPairRoundedFacts innerPair658Data innerPair658Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair658Input_eq }

noncomputable def innerPair659Data : WideLogData :=
  { lower := endpoint404
    upper := endpoint405 }

noncomputable def innerPair659Input : RationalEnclosure :=
  { lower := (14198907/16777216), upper := (14394563/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair659Input_eq :
    innerPair659Input = outerEnclosure 24 innerPair659Data.output := by
  rfl'

theorem innerPair659RoundedFacts :
    InnerPairRoundedFacts innerPair659Data innerPair659Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair659Input_eq }

noncomputable def innerPair660Data : WideLogData :=
  { lower := endpoint406
    upper := endpoint407 }

noncomputable def innerPair660Input : RationalEnclosure :=
  { lower := (14387613/16777216), upper := (14581093/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair660Input_eq :
    innerPair660Input = outerEnclosure 24 innerPair660Data.output := by
  rfl'

theorem innerPair660RoundedFacts :
    InnerPairRoundedFacts innerPair660Data innerPair660Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair660Input_eq }

noncomputable def innerPair661Data : WideLogData :=
  { lower := endpoint408
    upper := endpoint409 }

noncomputable def innerPair661Input : RationalEnclosure :=
  { lower := (1810579/2097152), upper := (14704305/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair661Input_eq :
    innerPair661Input = outerEnclosure 24 innerPair661Data.output := by
  rfl'

theorem innerPair661RoundedFacts :
    InnerPairRoundedFacts innerPair661Data innerPair661Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair661Input_eq }

noncomputable def innerPair662Data : WideLogData :=
  { lower := endpoint410
    upper := endpoint411 }

noncomputable def innerPair662Input : RationalEnclosure :=
  { lower := (3643555/4194304), upper := (14765573/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair662Input_eq :
    innerPair662Input = outerEnclosure 24 innerPair662Data.output := by
  rfl'

theorem innerPair662RoundedFacts :
    InnerPairRoundedFacts innerPair662Data innerPair662Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair662Input_eq }

noncomputable def innerPair663Data : WideLogData :=
  { lower := endpoint412
    upper := endpoint413 }

noncomputable def innerPair663Input : RationalEnclosure :=
  { lower := (14677001/16777216), upper := (7447093/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair663Input_eq :
    innerPair663Input = outerEnclosure 24 innerPair663Data.output := by
  rfl'

theorem innerPair663RoundedFacts :
    InnerPairRoundedFacts innerPair663Data innerPair663Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair663Input_eq }

noncomputable def innerPair664Data : WideLogData :=
  { lower := endpoint412
    upper := endpoint474 }

noncomputable def innerPair664Input : RationalEnclosure :=
  { lower := (14677001/16777216), upper := (3803695/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair664Input_eq :
    innerPair664Input = outerEnclosure 24 innerPair664Data.output := by
  rfl'

theorem innerPair664RoundedFacts :
    InnerPairRoundedFacts innerPair664Data innerPair664Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair664Input_eq }

noncomputable def innerPair665Data : WideLogData :=
  { lower := endpoint413
    upper := endpoint417 }

noncomputable def innerPair665Input : RationalEnclosure :=
  { lower := (14894185/16777216), upper := (15108595/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair665Input_eq :
    innerPair665Input = outerEnclosure 24 innerPair665Data.output := by
  rfl'

theorem innerPair665RoundedFacts :
    InnerPairRoundedFacts innerPair665Data innerPair665Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair665Input_eq }

noncomputable def innerPair666Data : WideLogData :=
  { lower := endpoint413
    upper := endpoint427 }

noncomputable def innerPair666Input : RationalEnclosure :=
  { lower := (14894185/16777216), upper := (15188297/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair666Input_eq :
    innerPair666Input = outerEnclosure 24 innerPair666Data.output := by
  rfl'

theorem innerPair666RoundedFacts :
    InnerPairRoundedFacts innerPair666Data innerPair666Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair666Input_eq }

noncomputable def innerPair667Data : WideLogData :=
  { lower := endpoint414
    upper := endpoint419 }

noncomputable def innerPair667Input : RationalEnclosure :=
  { lower := (3816905/4194304), upper := (3869335/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair667Input_eq :
    innerPair667Input = outerEnclosure 24 innerPair667Data.output := by
  rfl'

theorem innerPair667RoundedFacts :
    InnerPairRoundedFacts innerPair667Data innerPair667Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair667Input_eq }

noncomputable def innerPair668Data : WideLogData :=
  { lower := endpoint414
    upper := endpoint434 }

noncomputable def innerPair668Input : RationalEnclosure :=
  { lower := (3816905/4194304), upper := (1947653/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair668Input_eq :
    innerPair668Input = outerEnclosure 24 innerPair668Data.output := by
  rfl'

theorem innerPair668RoundedFacts :
    InnerPairRoundedFacts innerPair668Data innerPair668Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair668Input_eq }

noncomputable def innerPair669Data : WideLogData :=
  { lower := endpoint414
    upper := endpoint437 }

noncomputable def innerPair669Input : RationalEnclosure :=
  { lower := (3816905/4194304), upper := (3921117/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair669Input_eq :
    innerPair669Input = outerEnclosure 24 innerPair669Data.output := by
  rfl'

theorem innerPair669RoundedFacts :
    InnerPairRoundedFacts innerPair669Data innerPair669Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair669Input_eq }

noncomputable def innerPair670Data : WideLogData :=
  { lower := endpoint415
    upper := endpoint416 }

noncomputable def innerPair670Input : RationalEnclosure :=
  { lower := (14785945/16777216), upper := (15001733/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair670Input_eq :
    innerPair670Input = outerEnclosure 24 innerPair670Data.output := by
  rfl'

theorem innerPair670RoundedFacts :
    InnerPairRoundedFacts innerPair670Data innerPair670Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair670Input_eq }

noncomputable def innerPair671Data : WideLogData :=
  { lower := endpoint419
    upper := endpoint435 }

noncomputable def innerPair671Input : RationalEnclosure :=
  { lower := (7738669/8388608), upper := (15889071/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair671Input_eq :
    innerPair671Input = outerEnclosure 24 innerPair671Data.output := by
  rfl'

theorem innerPair671RoundedFacts :
    InnerPairRoundedFacts innerPair671Data innerPair671Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair671Input_eq }

noncomputable def innerPair672Data : WideLogData :=
  { lower := endpoint419
    upper := endpoint436 }

noncomputable def innerPair672Input : RationalEnclosure :=
  { lower := (7738669/8388608), upper := (3997611/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair672Input_eq :
    innerPair672Input = outerEnclosure 24 innerPair672Data.output := by
  rfl'

theorem innerPair672RoundedFacts :
    InnerPairRoundedFacts innerPair672Data innerPair672Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair672Input_eq }

noncomputable def innerPair673Data : WideLogData :=
  { lower := endpoint419
    upper := endpoint444 }

noncomputable def innerPair673Input : RationalEnclosure :=
  { lower := (7738669/8388608), upper := (16091209/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair673Input_eq :
    innerPair673Input = outerEnclosure 24 innerPair673Data.output := by
  rfl'

theorem innerPair673RoundedFacts :
    InnerPairRoundedFacts innerPair673Data innerPair673Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair673Input_eq }

noncomputable def innerPair674Data : WideLogData :=
  { lower := endpoint419
    upper := endpoint473 }

noncomputable def innerPair674Input : RationalEnclosure :=
  { lower := (7738669/8388608), upper := (16241229/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair674Input_eq :
    innerPair674Input = outerEnclosure 24 innerPair674Data.output := by
  rfl'

theorem innerPair674RoundedFacts :
    InnerPairRoundedFacts innerPair674Data innerPair674Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair674Input_eq }

noncomputable def innerPair675Data : WideLogData :=
  { lower := endpoint420
    upper := endpoint421 }

noncomputable def innerPair675Input : RationalEnclosure :=
  { lower := (14255041/16777216), upper := (14546707/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair675Input_eq :
    innerPair675Input = outerEnclosure 24 innerPair675Data.output := by
  rfl'

theorem innerPair675RoundedFacts :
    InnerPairRoundedFacts innerPair675Data innerPair675Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair675Input_eq }

noncomputable def innerPair676Data : WideLogData :=
  { lower := endpoint422
    upper := endpoint309 }

noncomputable def innerPair676Input : RationalEnclosure :=
  { lower := (14345861/16777216), upper := (14629117/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair676Input_eq :
    innerPair676Input = outerEnclosure 24 innerPair676Data.output := by
  rfl'

theorem innerPair676RoundedFacts :
    InnerPairRoundedFacts innerPair676Data innerPair676Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair676Input_eq }

noncomputable def innerPair677Data : WideLogData :=
  { lower := endpoint425
    upper := endpoint426 }

noncomputable def innerPair677Input : RationalEnclosure :=
  { lower := (7355561/8388608), upper := (1874379/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair677Input_eq :
    innerPair677Input = outerEnclosure 24 innerPair677Data.output := by
  rfl'

theorem innerPair677RoundedFacts :
    InnerPairRoundedFacts innerPair677Data innerPair677Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair677Input_eq }

noncomputable def innerPair678Data : WideLogData :=
  { lower := endpoint428
    upper := endpoint429 }

noncomputable def innerPair678Input : RationalEnclosure :=
  { lower := (7487455/8388608), upper := (3823495/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair678Input_eq :
    innerPair678Input = outerEnclosure 24 innerPair678Data.output := by
  rfl'

theorem innerPair678RoundedFacts :
    InnerPairRoundedFacts innerPair678Data innerPair678Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair678Input_eq }

noncomputable def innerPair679Data : WideLogData :=
  { lower := endpoint430
    upper := endpoint431 }

noncomputable def innerPair679Input : RationalEnclosure :=
  { lower := (1884409/2097152), upper := (959981/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair679Input_eq :
    innerPair679Input = outerEnclosure 24 innerPair679Data.output := by
  rfl'

theorem innerPair679RoundedFacts :
    InnerPairRoundedFacts innerPair679Data innerPair679Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair679Input_eq }

noncomputable def innerPair680Data : WideLogData :=
  { lower := endpoint432
    upper := endpoint433 }

noncomputable def innerPair680Input : RationalEnclosure :=
  { lower := (7540971/8388608), upper := (7699501/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair680Input_eq :
    innerPair680Input = outerEnclosure 24 innerPair680Data.output := by
  rfl'

theorem innerPair680RoundedFacts :
    InnerPairRoundedFacts innerPair680Data innerPair680Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair680Input_eq }

noncomputable def innerPair681Data : WideLogData :=
  { lower := endpoint434
    upper := endpoint435 }

noncomputable def innerPair681Input : RationalEnclosure :=
  { lower := (7790611/8388608), upper := (15889071/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair681Input_eq :
    innerPair681Input = outerEnclosure 24 innerPair681Data.output := by
  rfl'

theorem innerPair681RoundedFacts :
    InnerPairRoundedFacts innerPair681Data innerPair681Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair681Input_eq }

noncomputable def innerPair682Data : WideLogData :=
  { lower := endpoint434
    upper := endpoint436 }

noncomputable def innerPair682Input : RationalEnclosure :=
  { lower := (7790611/8388608), upper := (3997611/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair682Input_eq :
    innerPair682Input = outerEnclosure 24 innerPair682Data.output := by
  rfl'

theorem innerPair682RoundedFacts :
    InnerPairRoundedFacts innerPair682Data innerPair682Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair682Input_eq }

noncomputable def innerPair683Data : WideLogData :=
  { lower := endpoint434
    upper := endpoint444 }

noncomputable def innerPair683Input : RationalEnclosure :=
  { lower := (7790611/8388608), upper := (16091209/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair683Input_eq :
    innerPair683Input = outerEnclosure 24 innerPair683Data.output := by
  rfl'

theorem innerPair683RoundedFacts :
    InnerPairRoundedFacts innerPair683Data innerPair683Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair683Input_eq }

noncomputable def innerPair684Data : WideLogData :=
  { lower := endpoint435
    upper := endpoint95 }

noncomputable def innerPair684Input : RationalEnclosure :=
  { lower := (7944535/8388608), upper := (4072735/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair684Input_eq :
    innerPair684Input = outerEnclosure 24 innerPair684Data.output := by
  rfl'

theorem innerPair684RoundedFacts :
    InnerPairRoundedFacts innerPair684Data innerPair684Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair684Input_eq }

noncomputable def innerPair685Data : WideLogData :=
  { lower := endpoint435
    upper := endpoint447 }

noncomputable def innerPair685Input : RationalEnclosure :=
  { lower := (7944535/8388608), upper := (16389921/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair685Input_eq :
    innerPair685Input = outerEnclosure 24 innerPair685Data.output := by
  rfl'

theorem innerPair685RoundedFacts :
    InnerPairRoundedFacts innerPair685Data innerPair685Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair685Input_eq }

noncomputable def innerPair686Data : WideLogData :=
  { lower := endpoint435
    upper := endpoint448 }

noncomputable def innerPair686Input : RationalEnclosure :=
  { lower := (7944535/8388608), upper := (16488321/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair686Input_eq :
    innerPair686Input = outerEnclosure 24 innerPair686Data.output := by
  rfl'

theorem innerPair686RoundedFacts :
    InnerPairRoundedFacts innerPair686Data innerPair686Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair686Input_eq }

noncomputable def innerPair687Data : WideLogData :=
  { lower := endpoint435
    upper := endpoint461 }

noncomputable def innerPair687Input : RationalEnclosure :=
  { lower := (7944535/8388608), upper := (8390053/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair687Input_eq :
    innerPair687Input = outerEnclosure 24 innerPair687Data.output := by
  rfl'

theorem innerPair687RoundedFacts :
    InnerPairRoundedFacts innerPair687Data innerPair687Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair687Input_eq }

noncomputable def innerPair688Data : WideLogData :=
  { lower := endpoint436
    upper := endpoint95 }

noncomputable def innerPair688Input : RationalEnclosure :=
  { lower := (15990443/16777216), upper := (4072735/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair688Input_eq :
    innerPair688Input = outerEnclosure 24 innerPair688Data.output := by
  rfl'

theorem innerPair688RoundedFacts :
    InnerPairRoundedFacts innerPair688Data innerPair688Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair688Input_eq }

noncomputable def innerPair689Data : WideLogData :=
  { lower := endpoint436
    upper := endpoint447 }

noncomputable def innerPair689Input : RationalEnclosure :=
  { lower := (15990443/16777216), upper := (16389921/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair689Input_eq :
    innerPair689Input = outerEnclosure 24 innerPair689Data.output := by
  rfl'

theorem innerPair689RoundedFacts :
    InnerPairRoundedFacts innerPair689Data innerPair689Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair689Input_eq }

noncomputable def innerPair690Data : WideLogData :=
  { lower := endpoint436
    upper := endpoint448 }

noncomputable def innerPair690Input : RationalEnclosure :=
  { lower := (15990443/16777216), upper := (16488321/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair690Input_eq :
    innerPair690Input = outerEnclosure 24 innerPair690Data.output := by
  rfl'

theorem innerPair690RoundedFacts :
    InnerPairRoundedFacts innerPair690Data innerPair690Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair690Input_eq }

noncomputable def innerPair691Data : WideLogData :=
  { lower := endpoint437
    upper := endpoint95 }

noncomputable def innerPair691Input : RationalEnclosure :=
  { lower := (15684467/16777216), upper := (4072735/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair691Input_eq :
    innerPair691Input = outerEnclosure 24 innerPair691Data.output := by
  rfl'

theorem innerPair691RoundedFacts :
    InnerPairRoundedFacts innerPair691Data innerPair691Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair691Input_eq }

noncomputable def innerPair692Data : WideLogData :=
  { lower := endpoint437
    upper := endpoint435 }

noncomputable def innerPair692Input : RationalEnclosure :=
  { lower := (15684467/16777216), upper := (15889071/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair692Input_eq :
    innerPair692Input = outerEnclosure 24 innerPair692Data.output := by
  rfl'

theorem innerPair692RoundedFacts :
    InnerPairRoundedFacts innerPair692Data innerPair692Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair692Input_eq }

noncomputable def innerPair693Data : WideLogData :=
  { lower := endpoint437
    upper := endpoint436 }

noncomputable def innerPair693Input : RationalEnclosure :=
  { lower := (15684467/16777216), upper := (3997611/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair693Input_eq :
    innerPair693Input = outerEnclosure 24 innerPair693Data.output := by
  rfl'

theorem innerPair693RoundedFacts :
    InnerPairRoundedFacts innerPair693Data innerPair693Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair693Input_eq }

noncomputable def innerPair694Data : WideLogData :=
  { lower := endpoint437
    upper := endpoint444 }

noncomputable def innerPair694Input : RationalEnclosure :=
  { lower := (15684467/16777216), upper := (16091209/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair694Input_eq :
    innerPair694Input = outerEnclosure 24 innerPair694Data.output := by
  rfl'

theorem innerPair694RoundedFacts :
    InnerPairRoundedFacts innerPair694Data innerPair694Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair694Input_eq }

noncomputable def innerPair695Data : WideLogData :=
  { lower := endpoint438
    upper := endpoint439 }

noncomputable def innerPair695Input : RationalEnclosure :=
  { lower := (3836643/4194304), upper := (15658717/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair695Input_eq :
    innerPair695Input = outerEnclosure 24 innerPair695Data.output := by
  rfl'

theorem innerPair695RoundedFacts :
    InnerPairRoundedFacts innerPair695Data innerPair695Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair695Input_eq }

noncomputable def innerPair696Data : WideLogData :=
  { lower := endpoint440
    upper := endpoint441 }

noncomputable def innerPair696Input : RationalEnclosure :=
  { lower := (15438215/16777216), upper := (7861511/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair696Input_eq :
    innerPair696Input = outerEnclosure 24 innerPair696Data.output := by
  rfl'

theorem innerPair696RoundedFacts :
    InnerPairRoundedFacts innerPair696Data innerPair696Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair696Input_eq }

noncomputable def innerPair697Data : WideLogData :=
  { lower := endpoint442
    upper := endpoint443 }

noncomputable def innerPair697Input : RationalEnclosure :=
  { lower := (3908231/4194304), upper := (1989309/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair697Input_eq :
    innerPair697Input = outerEnclosure 24 innerPair697Data.output := by
  rfl'

theorem innerPair697RoundedFacts :
    InnerPairRoundedFacts innerPair697Data innerPair697Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair697Input_eq }

noncomputable def innerPair698Data : WideLogData :=
  { lower := endpoint444
    upper := endpoint95 }

noncomputable def innerPair698Input : RationalEnclosure :=
  { lower := (16091207/16777216), upper := (4072735/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair698Input_eq :
    innerPair698Input = outerEnclosure 24 innerPair698Data.output := by
  rfl'

theorem innerPair698RoundedFacts :
    InnerPairRoundedFacts innerPair698Data innerPair698Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair698Input_eq }

noncomputable def innerPair699Data : WideLogData :=
  { lower := endpoint444
    upper := endpoint447 }

noncomputable def innerPair699Input : RationalEnclosure :=
  { lower := (16091207/16777216), upper := (16389921/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair699Input_eq :
    innerPair699Input = outerEnclosure 24 innerPair699Data.output := by
  rfl'

theorem innerPair699RoundedFacts :
    InnerPairRoundedFacts innerPair699Data innerPair699Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair699Input_eq }

noncomputable def innerPair700Data : WideLogData :=
  { lower := endpoint444
    upper := endpoint448 }

noncomputable def innerPair700Input : RationalEnclosure :=
  { lower := (16091207/16777216), upper := (16488321/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair700Input_eq :
    innerPair700Input = outerEnclosure 24 innerPair700Data.output := by
  rfl'

theorem innerPair700RoundedFacts :
    InnerPairRoundedFacts innerPair700Data innerPair700Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair700Input_eq }

noncomputable def innerPair701Data : WideLogData :=
  { lower := endpoint445
    upper := endpoint446 }

noncomputable def innerPair701Input : RationalEnclosure :=
  { lower := (15710179/16777216), upper := (4003923/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair701Input_eq :
    innerPair701Input = outerEnclosure 24 innerPair701Data.output := by
  rfl'

theorem innerPair701RoundedFacts :
    InnerPairRoundedFacts innerPair701Data innerPair701Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair701Input_eq }

noncomputable def innerPair702Data : WideLogData :=
  { lower := endpoint447
    upper := endpoint451 }

noncomputable def innerPair702Input : RationalEnclosure :=
  { lower := (16389919/16777216), upper := (16683407/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair702Input_eq :
    innerPair702Input = outerEnclosure 24 innerPair702Data.output := by
  rfl'

theorem innerPair702RoundedFacts :
    InnerPairRoundedFacts innerPair702Data innerPair702Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair702Input_eq }

noncomputable def innerPair703Data : WideLogData :=
  { lower := endpoint447
    upper := endpoint461 }

noncomputable def innerPair703Input : RationalEnclosure :=
  { lower := (16389919/16777216), upper := (8390053/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair703Input_eq :
    innerPair703Input = outerEnclosure 24 innerPair703Data.output := by
  rfl'

theorem innerPair703RoundedFacts :
    InnerPairRoundedFacts innerPair703Data innerPair703Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair703Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
