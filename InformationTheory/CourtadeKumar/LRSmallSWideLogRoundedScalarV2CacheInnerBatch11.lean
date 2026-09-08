import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8

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

noncomputable def innerPair704Data : WideLogData :=
  { lower := endpoint448
    upper := endpoint460 }

noncomputable def innerPair704Input : RationalEnclosure :=
  { lower := (128815/131072), upper := (17066903/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair704Input_eq :
    innerPair704Input = outerEnclosure 24 innerPair704Data.output := by
  rfl'

theorem innerPair704RoundedFacts :
    InnerPairRoundedFacts innerPair704Data innerPair704Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair704Input_eq }

noncomputable def innerPair705Data : WideLogData :=
  { lower := endpoint448
    upper := endpoint462 }

noncomputable def innerPair705Input : RationalEnclosure :=
  { lower := (128815/131072), upper := (16876251/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair705Input_eq :
    innerPair705Input = outerEnclosure 24 innerPair705Data.output := by
  rfl'

theorem innerPair705RoundedFacts :
    InnerPairRoundedFacts innerPair705Data innerPair705Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair705Input_eq }

noncomputable def innerPair706Data : WideLogData :=
  { lower := endpoint448
    upper := endpoint467 }

noncomputable def innerPair706Input : RationalEnclosure :=
  { lower := (128815/131072), upper := (17255413/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair706Input_eq :
    innerPair706Input = outerEnclosure 24 innerPair706Data.output := by
  rfl'

theorem innerPair706RoundedFacts :
    InnerPairRoundedFacts innerPair706Data innerPair706Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair706Input_eq }

noncomputable def innerPair707Data : WideLogData :=
  { lower := endpoint449
    upper := endpoint450 }

noncomputable def innerPair707Input : RationalEnclosure :=
  { lower := (16166385/16777216), upper := (8222671/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair707Input_eq :
    innerPair707Input = outerEnclosure 24 innerPair707Data.output := by
  rfl'

theorem innerPair707RoundedFacts :
    InnerPairRoundedFacts innerPair707Data innerPair707Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair707Input_eq }

noncomputable def innerPair708Data : WideLogData :=
  { lower := endpoint451
    upper := endpoint460 }

noncomputable def innerPair708Input : RationalEnclosure :=
  { lower := (8341703/8388608), upper := (17066903/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair708Input_eq :
    innerPair708Input = outerEnclosure 24 innerPair708Data.output := by
  rfl'

theorem innerPair708RoundedFacts :
    InnerPairRoundedFacts innerPair708Data innerPair708Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair708Input_eq }

noncomputable def innerPair709Data : WideLogData :=
  { lower := endpoint451
    upper := endpoint463 }

noncomputable def innerPair709Input : RationalEnclosure :=
  { lower := (8341703/8388608), upper := (17161423/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair709Input_eq :
    innerPair709Input = outerEnclosure 24 innerPair709Data.output := by
  rfl'

theorem innerPair709RoundedFacts :
    InnerPairRoundedFacts innerPair709Data innerPair709Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair709Input_eq }

noncomputable def innerPair710Data : WideLogData :=
  { lower := endpoint451
    upper := endpoint464 }

noncomputable def innerPair710Input : RationalEnclosure :=
  { lower := (8341703/8388608), upper := (17441829/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair710Input_eq :
    innerPair710Input = outerEnclosure 24 innerPair710Data.output := by
  rfl'

theorem innerPair710RoundedFacts :
    InnerPairRoundedFacts innerPair710Data innerPair710Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair710Input_eq }

noncomputable def innerPair711Data : WideLogData :=
  { lower := endpoint451
    upper := endpoint480 }

noncomputable def innerPair711Input : RationalEnclosure :=
  { lower := (8341703/8388608), upper := (17231965/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair711Input_eq :
    innerPair711Input = outerEnclosure 24 innerPair711Data.output := by
  rfl'

theorem innerPair711RoundedFacts :
    InnerPairRoundedFacts innerPair711Data innerPair711Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair711Input_eq }

noncomputable def innerPair712Data : WideLogData :=
  { lower := endpoint452
    upper := endpoint453 }

noncomputable def innerPair712Input : RationalEnclosure :=
  { lower := (16252115/16777216), upper := (16529661/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair712Input_eq :
    innerPair712Input = outerEnclosure 24 innerPair712Data.output := by
  rfl'

theorem innerPair712RoundedFacts :
    InnerPairRoundedFacts innerPair712Data innerPair712Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair712Input_eq }

noncomputable def innerPair713Data : WideLogData :=
  { lower := endpoint454
    upper := endpoint455 }

noncomputable def innerPair713Input : RationalEnclosure :=
  { lower := (2054899/2097152), upper := (8365913/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair713Input_eq :
    innerPair713Input = outerEnclosure 24 innerPair713Data.output := by
  rfl'

theorem innerPair713RoundedFacts :
    InnerPairRoundedFacts innerPair713Data innerPair713Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair713Input_eq }

noncomputable def innerPair714Data : WideLogData :=
  { lower := endpoint456
    upper := endpoint457 }

noncomputable def innerPair714Input : RationalEnclosure :=
  { lower := (8256415/8388608), upper := (8402097/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair714Input_eq :
    innerPair714Input = outerEnclosure 24 innerPair714Data.output := by
  rfl'

theorem innerPair714RoundedFacts :
    InnerPairRoundedFacts innerPair714Data innerPair714Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair714Input_eq }

noncomputable def innerPair715Data : WideLogData :=
  { lower := endpoint457
    upper := endpoint518 }

noncomputable def innerPair715Input : RationalEnclosure :=
  { lower := (16804193/16777216), upper := (4302121/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair715Input_eq :
    innerPair715Input = outerEnclosure 24 innerPair715Data.output := by
  rfl'

theorem innerPair715RoundedFacts :
    InnerPairRoundedFacts innerPair715Data innerPair715Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair715Input_eq }

noncomputable def innerPair716Data : WideLogData :=
  { lower := endpoint458
    upper := endpoint459 }

noncomputable def innerPair716Input : RationalEnclosure :=
  { lower := (8305257/8388608), upper := (8444115/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair716Input_eq :
    innerPair716Input = outerEnclosure 24 innerPair716Data.output := by
  rfl'

theorem innerPair716RoundedFacts :
    InnerPairRoundedFacts innerPair716Data innerPair716Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair716Input_eq }

noncomputable def innerPair717Data : WideLogData :=
  { lower := endpoint458
    upper := endpoint466 }

noncomputable def innerPair717Input : RationalEnclosure :=
  { lower := (8305257/8388608), upper := (8497831/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair717Input_eq :
    innerPair717Input = outerEnclosure 24 innerPair717Data.output := by
  rfl'

theorem innerPair717RoundedFacts :
    InnerPairRoundedFacts innerPair717Data innerPair717Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair717Input_eq }

noncomputable def innerPair718Data : WideLogData :=
  { lower := endpoint460
    upper := endpoint464 }

noncomputable def innerPair718Input : RationalEnclosure :=
  { lower := (8533451/8388608), upper := (17441829/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair718Input_eq :
    innerPair718Input = outerEnclosure 24 innerPair718Data.output := by
  rfl'

theorem innerPair718RoundedFacts :
    InnerPairRoundedFacts innerPair718Data innerPair718Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair718Input_eq }

noncomputable def innerPair719Data : WideLogData :=
  { lower := endpoint460
    upper := endpoint469 }

noncomputable def innerPair719Input : RationalEnclosure :=
  { lower := (8533451/8388608), upper := (17534265/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair719Input_eq :
    innerPair719Input = outerEnclosure 24 innerPair719Data.output := by
  rfl'

theorem innerPair719RoundedFacts :
    InnerPairRoundedFacts innerPair719Data innerPair719Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair719Input_eq }

noncomputable def innerPair720Data : WideLogData :=
  { lower := endpoint461
    upper := endpoint463 }

noncomputable def innerPair720Input : RationalEnclosure :=
  { lower := (16780105/16777216), upper := (17161423/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair720Input_eq :
    innerPair720Input = outerEnclosure 24 innerPair720Data.output := by
  rfl'

theorem innerPair720RoundedFacts :
    InnerPairRoundedFacts innerPair720Data innerPair720Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair720Input_eq }

noncomputable def innerPair721Data : WideLogData :=
  { lower := endpoint461
    upper := endpoint468 }

noncomputable def innerPair721Input : RationalEnclosure :=
  { lower := (16780105/16777216), upper := (17090583/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair721Input_eq :
    innerPair721Input = outerEnclosure 24 innerPair721Data.output := by
  rfl'

theorem innerPair721RoundedFacts :
    InnerPairRoundedFacts innerPair721Data innerPair721Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair721Input_eq }

noncomputable def innerPair722Data : WideLogData :=
  { lower := endpoint462
    upper := endpoint463 }

noncomputable def innerPair722Input : RationalEnclosure :=
  { lower := (8438125/8388608), upper := (17161423/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair722Input_eq :
    innerPair722Input = outerEnclosure 24 innerPair722Data.output := by
  rfl'

theorem innerPair722RoundedFacts :
    InnerPairRoundedFacts innerPair722Data innerPair722Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair722Input_eq }

noncomputable def innerPair723Data : WideLogData :=
  { lower := endpoint462
    upper := endpoint467 }

noncomputable def innerPair723Input : RationalEnclosure :=
  { lower := (8438125/8388608), upper := (17255413/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair723Input_eq :
    innerPair723Input = outerEnclosure 24 innerPair723Data.output := by
  rfl'

theorem innerPair723RoundedFacts :
    InnerPairRoundedFacts innerPair723Data innerPair723Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair723Input_eq }

noncomputable def innerPair724Data : WideLogData :=
  { lower := endpoint463
    upper := endpoint469 }

noncomputable def innerPair724Input : RationalEnclosure :=
  { lower := (8580711/8388608), upper := (17534265/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair724Input_eq :
    innerPair724Input = outerEnclosure 24 innerPair724Data.output := by
  rfl'

theorem innerPair724RoundedFacts :
    InnerPairRoundedFacts innerPair724Data innerPair724Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair724Input_eq }

noncomputable def innerPair725Data : WideLogData :=
  { lower := endpoint463
    upper := endpoint470 }

noncomputable def innerPair725Input : RationalEnclosure :=
  { lower := (8580711/8388608), upper := (8904279/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair725Input_eq :
    innerPair725Input = outerEnclosure 24 innerPair725Data.output := by
  rfl'

theorem innerPair725RoundedFacts :
    InnerPairRoundedFacts innerPair725Data innerPair725Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair725Input_eq }

noncomputable def innerPair726Data : WideLogData :=
  { lower := endpoint464
    upper := endpoint470 }

noncomputable def innerPair726Input : RationalEnclosure :=
  { lower := (17441827/16777216), upper := (8904279/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair726Input_eq :
    innerPair726Input = outerEnclosure 24 innerPair726Data.output := by
  rfl'

theorem innerPair726RoundedFacts :
    InnerPairRoundedFacts innerPair726Data innerPair726Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair726Input_eq }

noncomputable def innerPair727Data : WideLogData :=
  { lower := endpoint464
    upper := endpoint471 }

noncomputable def innerPair727Input : RationalEnclosure :=
  { lower := (17441827/16777216), upper := (8949501/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair727Input_eq :
    innerPair727Input = outerEnclosure 24 innerPair727Data.output := by
  rfl'

theorem innerPair727RoundedFacts :
    InnerPairRoundedFacts innerPair727Data innerPair727Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair727Input_eq }

noncomputable def innerPair728Data : WideLogData :=
  { lower := endpoint464
    upper := endpoint481 }

noncomputable def innerPair728Input : RationalEnclosure :=
  { lower := (17441827/16777216), upper := (18255977/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair728Input_eq :
    innerPair728Input = outerEnclosure 24 innerPair728Data.output := by
  rfl'

theorem innerPair728RoundedFacts :
    InnerPairRoundedFacts innerPair728Data innerPair728Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair728Input_eq }

noncomputable def innerPair729Data : WideLogData :=
  { lower := endpoint465
    upper := endpoint466 }

noncomputable def innerPair729Input : RationalEnclosure :=
  { lower := (16707633/16777216), upper := (8497831/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair729Input_eq :
    innerPair729Input = outerEnclosure 24 innerPair729Data.output := by
  rfl'

theorem innerPair729RoundedFacts :
    InnerPairRoundedFacts innerPair729Data innerPair729Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair729Input_eq }

noncomputable def innerPair730Data : WideLogData :=
  { lower := endpoint467
    upper := endpoint469 }

noncomputable def innerPair730Input : RationalEnclosure :=
  { lower := (4313853/4194304), upper := (17534265/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair730Input_eq :
    innerPair730Input = outerEnclosure 24 innerPair730Data.output := by
  rfl'

theorem innerPair730RoundedFacts :
    InnerPairRoundedFacts innerPair730Data innerPair730Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair730Input_eq }

noncomputable def innerPair731Data : WideLogData :=
  { lower := endpoint469
    upper := endpoint471 }

noncomputable def innerPair731Input : RationalEnclosure :=
  { lower := (2191783/2097152), upper := (8949501/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair731Input_eq :
    innerPair731Input = outerEnclosure 24 innerPair731Data.output := by
  rfl'

theorem innerPair731RoundedFacts :
    InnerPairRoundedFacts innerPair731Data innerPair731Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair731Input_eq }

noncomputable def innerPair732Data : WideLogData :=
  { lower := endpoint469
    upper := endpoint523 }

noncomputable def innerPair732Input : RationalEnclosure :=
  { lower := (2191783/2097152), upper := (17921537/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair732Input_eq :
    innerPair732Input = outerEnclosure 24 innerPair732Data.output := by
  rfl'

theorem innerPair732RoundedFacts :
    InnerPairRoundedFacts innerPair732Data innerPair732Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair732Input_eq }

noncomputable def innerPair733Data : WideLogData :=
  { lower := endpoint470
    upper := endpoint472 }

noncomputable def innerPair733Input : RationalEnclosure :=
  { lower := (17808557/16777216), upper := (18167443/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair733Input_eq :
    innerPair733Input = outerEnclosure 24 innerPair733Data.output := by
  rfl'

theorem innerPair733RoundedFacts :
    InnerPairRoundedFacts innerPair733Data innerPair733Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair733Input_eq }

noncomputable def innerPair734Data : WideLogData :=
  { lower := endpoint470
    upper := endpoint481 }

noncomputable def innerPair734Input : RationalEnclosure :=
  { lower := (17808557/16777216), upper := (18255977/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair734Input_eq :
    innerPair734Input = outerEnclosure 24 innerPair734Data.output := by
  rfl'

theorem innerPair734RoundedFacts :
    InnerPairRoundedFacts innerPair734Data innerPair734Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair734Input_eq }

noncomputable def innerPair735Data : WideLogData :=
  { lower := endpoint471
    upper := endpoint481 }

noncomputable def innerPair735Input : RationalEnclosure :=
  { lower := (2237375/2097152), upper := (18255977/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair735Input_eq :
    innerPair735Input = outerEnclosure 24 innerPair735Data.output := by
  rfl'

theorem innerPair735RoundedFacts :
    InnerPairRoundedFacts innerPair735Data innerPair735Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair735Input_eq }

noncomputable def innerPair736Data : WideLogData :=
  { lower := endpoint471
    upper := endpoint491 }

noncomputable def innerPair736Input : RationalEnclosure :=
  { lower := (2237375/2097152), upper := (18518811/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair736Input_eq :
    innerPair736Input = outerEnclosure 24 innerPair736Data.output := by
  rfl'

theorem innerPair736RoundedFacts :
    InnerPairRoundedFacts innerPair736Data innerPair736Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair736Input_eq }

noncomputable def innerPair737Data : WideLogData :=
  { lower := endpoint472
    upper := endpoint526 }

noncomputable def innerPair737Input : RationalEnclosure :=
  { lower := (9083721/8388608), upper := (18605515/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair737Input_eq :
    innerPair737Input = outerEnclosure 24 innerPair737Data.output := by
  rfl'

theorem innerPair737RoundedFacts :
    InnerPairRoundedFacts innerPair737Data innerPair737Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair737Input_eq }

noncomputable def innerPair738Data : WideLogData :=
  { lower := endpoint473
    upper := endpoint514 }

noncomputable def innerPair738Input : RationalEnclosure :=
  { lower := (4060307/4194304), upper := (519839/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair738Input_eq :
    innerPair738Input = outerEnclosure 24 innerPair738Data.output := by
  rfl'

theorem innerPair738RoundedFacts :
    InnerPairRoundedFacts innerPair738Data innerPair738Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair738Input_eq }

noncomputable def innerPair739Data : WideLogData :=
  { lower := endpoint475
    upper := endpoint476 }

noncomputable def innerPair739Input : RationalEnclosure :=
  { lower := (7712577/8388608), upper := (7982579/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair739Input_eq :
    innerPair739Input = outerEnclosure 24 innerPair739Data.output := by
  rfl'

theorem innerPair739RoundedFacts :
    InnerPairRoundedFacts innerPair739Data innerPair739Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair739Input_eq }

noncomputable def innerPair740Data : WideLogData :=
  { lower := endpoint477
    upper := endpoint478 }

noncomputable def innerPair740Input : RationalEnclosure :=
  { lower := (15135203/16777216), upper := (7764681/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair740Input_eq :
    innerPair740Input = outerEnclosure 24 innerPair740Data.output := by
  rfl'

theorem innerPair740RoundedFacts :
    InnerPairRoundedFacts innerPair740Data innerPair740Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair740Input_eq }

noncomputable def innerPair741Data : WideLogData :=
  { lower := endpoint479
    upper := endpoint466 }

noncomputable def innerPair741Input : RationalEnclosure :=
  { lower := (8231887/8388608), upper := (8497831/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair741Input_eq :
    innerPair741Input = outerEnclosure 24 innerPair741Data.output := by
  rfl'

theorem innerPair741RoundedFacts :
    InnerPairRoundedFacts innerPair741Data innerPair741Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair741Input_eq }

noncomputable def innerPair742Data : WideLogData :=
  { lower := endpoint479
    upper := endpoint515 }

noncomputable def innerPair742Input : RationalEnclosure :=
  { lower := (8231887/8388608), upper := (16828247/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair742Input_eq :
    innerPair742Input = outerEnclosure 24 innerPair742Data.output := by
  rfl'

theorem innerPair742RoundedFacts :
    InnerPairRoundedFacts innerPair742Data innerPair742Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair742Input_eq }

noncomputable def innerPair743Data : WideLogData :=
  { lower := endpoint482
    upper := endpoint483 }

noncomputable def innerPair743Input : RationalEnclosure :=
  { lower := (18777589/16777216), upper := (2389567/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair743Input_eq :
    innerPair743Input = outerEnclosure 24 innerPair743Data.output := by
  rfl'

theorem innerPair743RoundedFacts :
    InnerPairRoundedFacts innerPair743Data innerPair743Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair743Input_eq }

noncomputable def innerPair744Data : WideLogData :=
  { lower := endpoint482
    upper := endpoint484 }

noncomputable def innerPair744Input : RationalEnclosure :=
  { lower := (18777589/16777216), upper := (19448769/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair744Input_eq :
    innerPair744Input = outerEnclosure 24 innerPair744Data.output := by
  rfl'

theorem innerPair744RoundedFacts :
    InnerPairRoundedFacts innerPair744Data innerPair744Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair744Input_eq }

noncomputable def innerPair745Data : WideLogData :=
  { lower := endpoint482
    upper := endpoint485 }

noncomputable def innerPair745Input : RationalEnclosure :=
  { lower := (18777589/16777216), upper := (9887275/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair745Input_eq :
    innerPair745Input = outerEnclosure 24 innerPair745Data.output := by
  rfl'

theorem innerPair745RoundedFacts :
    InnerPairRoundedFacts innerPair745Data innerPair745Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair745Input_eq }

noncomputable def innerPair746Data : WideLogData :=
  { lower := endpoint482
    upper := endpoint492 }

noncomputable def innerPair746Input : RationalEnclosure :=
  { lower := (18777589/16777216), upper := (19283475/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair746Input_eq :
    innerPair746Input = outerEnclosure 24 innerPair746Data.output := by
  rfl'

theorem innerPair746RoundedFacts :
    InnerPairRoundedFacts innerPair746Data innerPair746Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair746Input_eq }

noncomputable def innerPair747Data : WideLogData :=
  { lower := endpoint482
    upper := endpoint528 }

noncomputable def innerPair747Input : RationalEnclosure :=
  { lower := (18777589/16777216), upper := (19200213/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair747Input_eq :
    innerPair747Input = outerEnclosure 24 innerPair747Data.output := by
  rfl'

theorem innerPair747RoundedFacts :
    InnerPairRoundedFacts innerPair747Data innerPair747Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair747Input_eq }

noncomputable def innerPair748Data : WideLogData :=
  { lower := endpoint483
    upper := endpoint484 }

noncomputable def innerPair748Input : RationalEnclosure :=
  { lower := (19116535/16777216), upper := (19448769/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair748Input_eq :
    innerPair748Input = outerEnclosure 24 innerPair748Data.output := by
  rfl'

theorem innerPair748RoundedFacts :
    InnerPairRoundedFacts innerPair748Data innerPair748Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair748Input_eq }

noncomputable def innerPair749Data : WideLogData :=
  { lower := endpoint483
    upper := endpoint485 }

noncomputable def innerPair749Input : RationalEnclosure :=
  { lower := (19116535/16777216), upper := (9887275/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair749Input_eq :
    innerPair749Input = outerEnclosure 24 innerPair749Data.output := by
  rfl'

theorem innerPair749RoundedFacts :
    InnerPairRoundedFacts innerPair749Data innerPair749Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair749Input_eq }

noncomputable def innerPair750Data : WideLogData :=
  { lower := endpoint483
    upper := endpoint486 }

noncomputable def innerPair750Input : RationalEnclosure :=
  { lower := (19116535/16777216), upper := (10047063/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair750Input_eq :
    innerPair750Input = outerEnclosure 24 innerPair750Data.output := by
  rfl'

theorem innerPair750RoundedFacts :
    InnerPairRoundedFacts innerPair750Data innerPair750Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair750Input_eq }

noncomputable def innerPair751Data : WideLogData :=
  { lower := endpoint483
    upper := endpoint487 }

noncomputable def innerPair751Input : RationalEnclosure :=
  { lower := (19116535/16777216), upper := (1275483/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair751Input_eq :
    innerPair751Input = outerEnclosure 24 innerPair751Data.output := by
  rfl'

theorem innerPair751RoundedFacts :
    InnerPairRoundedFacts innerPair751Data innerPair751Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair751Input_eq }

noncomputable def innerPair752Data : WideLogData :=
  { lower := endpoint483
    upper := endpoint494 }

noncomputable def innerPair752Input : RationalEnclosure :=
  { lower := (19116535/16777216), upper := (19530809/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair752Input_eq :
    innerPair752Input = outerEnclosure 24 innerPair752Data.output := by
  rfl'

theorem innerPair752RoundedFacts :
    InnerPairRoundedFacts innerPair752Data innerPair752Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair752Input_eq }

noncomputable def innerPair753Data : WideLogData :=
  { lower := endpoint483
    upper := endpoint496 }

noncomputable def innerPair753Input : RationalEnclosure :=
  { lower := (19116535/16777216), upper := (153857/131072) }

set_option maxRecDepth 1000000 in
private theorem innerPair753Input_eq :
    innerPair753Input = outerEnclosure 24 innerPair753Data.output := by
  rfl'

theorem innerPair753RoundedFacts :
    InnerPairRoundedFacts innerPair753Data innerPair753Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair753Input_eq }

noncomputable def innerPair754Data : WideLogData :=
  { lower := endpoint484
    upper := endpoint485 }

noncomputable def innerPair754Input : RationalEnclosure :=
  { lower := (303887/262144), upper := (9887275/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair754Input_eq :
    innerPair754Input = outerEnclosure 24 innerPair754Data.output := by
  rfl'

theorem innerPair754RoundedFacts :
    InnerPairRoundedFacts innerPair754Data innerPair754Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair754Input_eq }

noncomputable def innerPair755Data : WideLogData :=
  { lower := endpoint484
    upper := endpoint486 }

noncomputable def innerPair755Input : RationalEnclosure :=
  { lower := (303887/262144), upper := (10047063/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair755Input_eq :
    innerPair755Input = outerEnclosure 24 innerPair755Data.output := by
  rfl'

theorem innerPair755RoundedFacts :
    InnerPairRoundedFacts innerPair755Data innerPair755Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair755Input_eq }

noncomputable def innerPair756Data : WideLogData :=
  { lower := endpoint484
    upper := endpoint487 }

noncomputable def innerPair756Input : RationalEnclosure :=
  { lower := (303887/262144), upper := (1275483/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair756Input_eq :
    innerPair756Input = outerEnclosure 24 innerPair756Data.output := by
  rfl'

theorem innerPair756RoundedFacts :
    InnerPairRoundedFacts innerPair756Data innerPair756Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair756Input_eq }

noncomputable def innerPair757Data : WideLogData :=
  { lower := endpoint484
    upper := endpoint488 }

noncomputable def innerPair757Input : RationalEnclosure :=
  { lower := (303887/262144), upper := (20715575/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair757Input_eq :
    innerPair757Input = outerEnclosure 24 innerPair757Data.output := by
  rfl'

theorem innerPair757RoundedFacts :
    InnerPairRoundedFacts innerPair757Data innerPair757Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair757Input_eq }

noncomputable def innerPair758Data : WideLogData :=
  { lower := endpoint484
    upper := endpoint495 }

noncomputable def innerPair758Input : RationalEnclosure :=
  { lower := (303887/262144), upper := (5062915/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair758Input_eq :
    innerPair758Input = outerEnclosure 24 innerPair758Data.output := by
  rfl'

theorem innerPair758RoundedFacts :
    InnerPairRoundedFacts innerPair758Data innerPair758Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair758Input_eq }

noncomputable def innerPair759Data : WideLogData :=
  { lower := endpoint484
    upper := endpoint554 }

noncomputable def innerPair759Input : RationalEnclosure :=
  { lower := (303887/262144), upper := (19855017/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair759Input_eq :
    innerPair759Input = outerEnclosure 24 innerPair759Data.output := by
  rfl'

theorem innerPair759RoundedFacts :
    InnerPairRoundedFacts innerPair759Data innerPair759Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair759Input_eq }

noncomputable def innerPair760Data : WideLogData :=
  { lower := endpoint485
    upper := endpoint486 }

noncomputable def innerPair760Input : RationalEnclosure :=
  { lower := (19774549/16777216), upper := (10047063/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair760Input_eq :
    innerPair760Input = outerEnclosure 24 innerPair760Data.output := by
  rfl'

theorem innerPair760RoundedFacts :
    InnerPairRoundedFacts innerPair760Data innerPair760Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair760Input_eq }

noncomputable def innerPair761Data : WideLogData :=
  { lower := endpoint485
    upper := endpoint487 }

noncomputable def innerPair761Input : RationalEnclosure :=
  { lower := (19774549/16777216), upper := (1275483/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair761Input_eq :
    innerPair761Input = outerEnclosure 24 innerPair761Data.output := by
  rfl'

theorem innerPair761RoundedFacts :
    InnerPairRoundedFacts innerPair761Data innerPair761Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair761Input_eq }

noncomputable def innerPair762Data : WideLogData :=
  { lower := endpoint485
    upper := endpoint488 }

noncomputable def innerPair762Input : RationalEnclosure :=
  { lower := (19774549/16777216), upper := (20715575/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair762Input_eq :
    innerPair762Input = outerEnclosure 24 innerPair762Data.output := by
  rfl'

theorem innerPair762RoundedFacts :
    InnerPairRoundedFacts innerPair762Data innerPair762Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair762Input_eq }

noncomputable def innerPair763Data : WideLogData :=
  { lower := endpoint485
    upper := endpoint495 }

noncomputable def innerPair763Input : RationalEnclosure :=
  { lower := (19774549/16777216), upper := (5062915/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair763Input_eq :
    innerPair763Input = outerEnclosure 24 innerPair763Data.output := by
  rfl'

theorem innerPair763RoundedFacts :
    InnerPairRoundedFacts innerPair763Data innerPair763Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair763Input_eq }

noncomputable def innerPair764Data : WideLogData :=
  { lower := endpoint485
    upper := endpoint536 }

noncomputable def innerPair764Input : RationalEnclosure :=
  { lower := (19774549/16777216), upper := (10086539/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair764Input_eq :
    innerPair764Input = outerEnclosure 24 innerPair764Data.output := by
  rfl'

theorem innerPair764RoundedFacts :
    InnerPairRoundedFacts innerPair764Data innerPair764Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair764Input_eq }

noncomputable def innerPair765Data : WideLogData :=
  { lower := endpoint486
    upper := endpoint488 }

noncomputable def innerPair765Input : RationalEnclosure :=
  { lower := (20094125/16777216), upper := (20715575/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair765Input_eq :
    innerPair765Input = outerEnclosure 24 innerPair765Data.output := by
  rfl'

theorem innerPair765RoundedFacts :
    InnerPairRoundedFacts innerPair765Data innerPair765Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair765Input_eq }

noncomputable def innerPair766Data : WideLogData :=
  { lower := endpoint486
    upper := endpoint489 }

noncomputable def innerPair766Input : RationalEnclosure :=
  { lower := (20094125/16777216), upper := (5254469/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair766Input_eq :
    innerPair766Input = outerEnclosure 24 innerPair766Data.output := by
  rfl'

theorem innerPair766RoundedFacts :
    InnerPairRoundedFacts innerPair766Data innerPair766Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair766Input_eq }

noncomputable def innerPair767Data : WideLogData :=
  { lower := endpoint486
    upper := endpoint497 }

noncomputable def innerPair767Input : RationalEnclosure :=
  { lower := (20094125/16777216), upper := (20485221/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair767Input_eq :
    innerPair767Input = outerEnclosure 24 innerPair767Data.output := by
  rfl'

theorem innerPair767RoundedFacts :
    InnerPairRoundedFacts innerPair767Data innerPair767Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair767Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
