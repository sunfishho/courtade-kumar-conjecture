import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch7
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch8
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch9

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

noncomputable def innerPair768Data : WideLogData :=
  { lower := endpoint486
    upper := endpoint498 }

noncomputable def innerPair768Input : RationalEnclosure :=
  { lower := (20094125/16777216), upper := (21314825/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair768Input_eq :
    innerPair768Input = outerEnclosure 24 innerPair768Data.output := by
  rfl'

theorem innerPair768RoundedFacts :
    InnerPairRoundedFacts innerPair768Data innerPair768Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair768Input_eq }

noncomputable def innerPair769Data : WideLogData :=
  { lower := endpoint486
    upper := endpoint540 }

noncomputable def innerPair769Input : RationalEnclosure :=
  { lower := (20094125/16777216), upper := (10281179/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair769Input_eq :
    innerPair769Input = outerEnclosure 24 innerPair769Data.output := by
  rfl'

theorem innerPair769RoundedFacts :
    InnerPairRoundedFacts innerPair769Data innerPair769Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair769Input_eq }

noncomputable def innerPair770Data : WideLogData :=
  { lower := endpoint487
    upper := endpoint489 }

noncomputable def innerPair770Input : RationalEnclosure :=
  { lower := (20407727/16777216), upper := (5254469/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair770Input_eq :
    innerPair770Input = outerEnclosure 24 innerPair770Data.output := by
  rfl'

theorem innerPair770RoundedFacts :
    InnerPairRoundedFacts innerPair770Data innerPair770Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair770Input_eq }

noncomputable def innerPair771Data : WideLogData :=
  { lower := endpoint487
    upper := endpoint498 }

noncomputable def innerPair771Input : RationalEnclosure :=
  { lower := (20407727/16777216), upper := (21314825/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair771Input_eq :
    innerPair771Input = outerEnclosure 24 innerPair771Data.output := by
  rfl'

theorem innerPair771RoundedFacts :
    InnerPairRoundedFacts innerPair771Data innerPair771Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair771Input_eq }

noncomputable def innerPair772Data : WideLogData :=
  { lower := endpoint487
    upper := endpoint499 }

noncomputable def innerPair772Input : RationalEnclosure :=
  { lower := (20407727/16777216), upper := (21167007/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair772Input_eq :
    innerPair772Input = outerEnclosure 24 innerPair772Data.output := by
  rfl'

theorem innerPair772RoundedFacts :
    InnerPairRoundedFacts innerPair772Data innerPair772Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair772Input_eq }

noncomputable def innerPair773Data : WideLogData :=
  { lower := endpoint487
    upper := endpoint500 }

noncomputable def innerPair773Input : RationalEnclosure :=
  { lower := (20407727/16777216), upper := (10803305/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair773Input_eq :
    innerPair773Input = outerEnclosure 24 innerPair773Data.output := by
  rfl'

theorem innerPair773RoundedFacts :
    InnerPairRoundedFacts innerPair773Data innerPair773Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair773Input_eq }

noncomputable def innerPair774Data : WideLogData :=
  { lower := endpoint487
    upper := endpoint559 }

noncomputable def innerPair774Input : RationalEnclosure :=
  { lower := (20407727/16777216), upper := (20791663/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair774Input_eq :
    innerPair774Input = outerEnclosure 24 innerPair774Data.output := by
  rfl'

theorem innerPair774RoundedFacts :
    InnerPairRoundedFacts innerPair774Data innerPair774Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair774Input_eq }

noncomputable def innerPair775Data : WideLogData :=
  { lower := endpoint488
    upper := endpoint498 }

noncomputable def innerPair775Input : RationalEnclosure :=
  { lower := (10357787/8388608), upper := (21314825/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair775Input_eq :
    innerPair775Input = outerEnclosure 24 innerPair775Data.output := by
  rfl'

theorem innerPair775RoundedFacts :
    InnerPairRoundedFacts innerPair775Data innerPair775Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair775Input_eq }

noncomputable def innerPair776Data : WideLogData :=
  { lower := endpoint488
    upper := endpoint500 }

noncomputable def innerPair776Input : RationalEnclosure :=
  { lower := (10357787/8388608), upper := (10803305/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair776Input_eq :
    innerPair776Input = outerEnclosure 24 innerPair776Data.output := by
  rfl'

theorem innerPair776RoundedFacts :
    InnerPairRoundedFacts innerPair776Data innerPair776Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair776Input_eq }

noncomputable def innerPair777Data : WideLogData :=
  { lower := endpoint488
    upper := endpoint501 }

noncomputable def innerPair777Input : RationalEnclosure :=
  { lower := (10357787/8388608), upper := (21893407/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair777Input_eq :
    innerPair777Input = outerEnclosure 24 innerPair777Data.output := by
  rfl'

theorem innerPair777RoundedFacts :
    InnerPairRoundedFacts innerPair777Data innerPair777Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair777Input_eq }

noncomputable def innerPair778Data : WideLogData :=
  { lower := endpoint489
    upper := endpoint500 }

noncomputable def innerPair778Input : RationalEnclosure :=
  { lower := (10508937/8388608), upper := (10803305/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair778Input_eq :
    innerPair778Input = outerEnclosure 24 innerPair778Data.output := by
  rfl'

theorem innerPair778RoundedFacts :
    InnerPairRoundedFacts innerPair778Data innerPair778Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair778Input_eq }

noncomputable def innerPair779Data : WideLogData :=
  { lower := endpoint489
    upper := endpoint501 }

noncomputable def innerPair779Input : RationalEnclosure :=
  { lower := (10508937/8388608), upper := (21893407/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair779Input_eq :
    innerPair779Input = outerEnclosure 24 innerPair779Data.output := by
  rfl'

theorem innerPair779RoundedFacts :
    InnerPairRoundedFacts innerPair779Data innerPair779Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair779Input_eq }

noncomputable def innerPair780Data : WideLogData :=
  { lower := endpoint489
    upper := endpoint502 }

noncomputable def innerPair780Input : RationalEnclosure :=
  { lower := (10508937/8388608), upper := (2771923/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair780Input_eq :
    innerPair780Input = outerEnclosure 24 innerPair780Data.output := by
  rfl'

theorem innerPair780RoundedFacts :
    InnerPairRoundedFacts innerPair780Data innerPair780Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair780Input_eq }

noncomputable def innerPair781Data : WideLogData :=
  { lower := endpoint490
    upper := endpoint481 }

noncomputable def innerPair781Input : RationalEnclosure :=
  { lower := (8813097/8388608), upper := (18255977/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair781Input_eq :
    innerPair781Input = outerEnclosure 24 innerPair781Data.output := by
  rfl'

theorem innerPair781RoundedFacts :
    InnerPairRoundedFacts innerPair781Data innerPair781Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair781Input_eq }

noncomputable def innerPair782Data : WideLogData :=
  { lower := endpoint490
    upper := endpoint491 }

noncomputable def innerPair782Input : RationalEnclosure :=
  { lower := (8813097/8388608), upper := (18518811/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair782Input_eq :
    innerPair782Input = outerEnclosure 24 innerPair782Data.output := by
  rfl'

theorem innerPair782RoundedFacts :
    InnerPairRoundedFacts innerPair782Data innerPair782Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair782Input_eq }

noncomputable def innerPair783Data : WideLogData :=
  { lower := endpoint491
    upper := endpoint530 }

noncomputable def innerPair783Input : RationalEnclosure :=
  { lower := (9259405/8388608), upper := (18947919/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair783Input_eq :
    innerPair783Input = outerEnclosure 24 innerPair783Data.output := by
  rfl'

theorem innerPair783RoundedFacts :
    InnerPairRoundedFacts innerPair783Data innerPair783Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair783Input_eq }

noncomputable def innerPair784Data : WideLogData :=
  { lower := endpoint492
    upper := endpoint496 }

noncomputable def innerPair784Input : RationalEnclosure :=
  { lower := (19283473/16777216), upper := (153857/131072) }

set_option maxRecDepth 1000000 in
private theorem innerPair784Input_eq :
    innerPair784Input = outerEnclosure 24 innerPair784Data.output := by
  rfl'

theorem innerPair784RoundedFacts :
    InnerPairRoundedFacts innerPair784Data innerPair784Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair784Input_eq }

noncomputable def innerPair785Data : WideLogData :=
  { lower := endpoint493
    upper := endpoint492 }

noncomputable def innerPair785Input : RationalEnclosure :=
  { lower := (4672943/4194304), upper := (19283475/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair785Input_eq :
    innerPair785Input = outerEnclosure 24 innerPair785Data.output := by
  rfl'

theorem innerPair785RoundedFacts :
    InnerPairRoundedFacts innerPair785Data innerPair785Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair785Input_eq }

noncomputable def innerPair786Data : WideLogData :=
  { lower := endpoint493
    upper := endpoint494 }

noncomputable def innerPair786Input : RationalEnclosure :=
  { lower := (4672943/4194304), upper := (19530809/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair786Input_eq :
    innerPair786Input = outerEnclosure 24 innerPair786Data.output := by
  rfl'

theorem innerPair786RoundedFacts :
    InnerPairRoundedFacts innerPair786Data innerPair786Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair786Input_eq }

noncomputable def innerPair787Data : WideLogData :=
  { lower := endpoint494
    upper := endpoint555 }

noncomputable def innerPair787Input : RationalEnclosure :=
  { lower := (2441351/2097152), upper := (19880083/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair787Input_eq :
    innerPair787Input = outerEnclosure 24 innerPair787Data.output := by
  rfl'

theorem innerPair787RoundedFacts :
    InnerPairRoundedFacts innerPair787Data innerPair787Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair787Input_eq }

noncomputable def innerPair788Data : WideLogData :=
  { lower := endpoint495
    upper := endpoint559 }

noncomputable def innerPair788Input : RationalEnclosure :=
  { lower := (10125829/8388608), upper := (20791663/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair788Input_eq :
    innerPair788Input = outerEnclosure 24 innerPair788Data.output := by
  rfl'

theorem innerPair788RoundedFacts :
    InnerPairRoundedFacts innerPair788Data innerPair788Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair788Input_eq }

noncomputable def innerPair789Data : WideLogData :=
  { lower := endpoint496
    upper := endpoint497 }

noncomputable def innerPair789Input : RationalEnclosure :=
  { lower := (19693695/16777216), upper := (20485221/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair789Input_eq :
    innerPair789Input = outerEnclosure 24 innerPair789Data.output := by
  rfl'

theorem innerPair789RoundedFacts :
    InnerPairRoundedFacts innerPair789Data innerPair789Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair789Input_eq }

noncomputable def innerPair790Data : WideLogData :=
  { lower := endpoint496
    upper := endpoint536 }

noncomputable def innerPair790Input : RationalEnclosure :=
  { lower := (19693695/16777216), upper := (10086539/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair790Input_eq :
    innerPair790Input = outerEnclosure 24 innerPair790Data.output := by
  rfl'

theorem innerPair790RoundedFacts :
    InnerPairRoundedFacts innerPair790Data innerPair790Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair790Input_eq }

noncomputable def innerPair791Data : WideLogData :=
  { lower := endpoint497
    upper := endpoint542 }

noncomputable def innerPair791Input : RationalEnclosure :=
  { lower := (5121305/4194304), upper := (10433703/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair791Input_eq :
    innerPair791Input = outerEnclosure 24 innerPair791Data.output := by
  rfl'

theorem innerPair791RoundedFacts :
    InnerPairRoundedFacts innerPair791Data innerPair791Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair791Input_eq }

noncomputable def innerPair792Data : WideLogData :=
  { lower := endpoint497
    upper := endpoint543 }

noncomputable def innerPair792Input : RationalEnclosure :=
  { lower := (5121305/4194304), upper := (21092607/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair792Input_eq :
    innerPair792Input = outerEnclosure 24 innerPair792Data.output := by
  rfl'

theorem innerPair792RoundedFacts :
    InnerPairRoundedFacts innerPair792Data innerPair792Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair792Input_eq }

noncomputable def innerPair793Data : WideLogData :=
  { lower := endpoint497
    upper := endpoint560 }

noncomputable def innerPair793Input : RationalEnclosure :=
  { lower := (5121305/4194304), upper := (20980385/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair793Input_eq :
    innerPair793Input = outerEnclosure 24 innerPair793Data.output := by
  rfl'

theorem innerPair793RoundedFacts :
    InnerPairRoundedFacts innerPair793Data innerPair793Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair793Input_eq }

noncomputable def innerPair794Data : WideLogData :=
  { lower := endpoint498
    upper := endpoint501 }

noncomputable def innerPair794Input : RationalEnclosure :=
  { lower := (2664353/2097152), upper := (21893407/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair794Input_eq :
    innerPair794Input = outerEnclosure 24 innerPair794Data.output := by
  rfl'

theorem innerPair794RoundedFacts :
    InnerPairRoundedFacts innerPair794Data innerPair794Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair794Input_eq }

noncomputable def innerPair795Data : WideLogData :=
  { lower := endpoint498
    upper := endpoint502 }

noncomputable def innerPair795Input : RationalEnclosure :=
  { lower := (2664353/2097152), upper := (2771923/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair795Input_eq :
    innerPair795Input = outerEnclosure 24 innerPair795Data.output := by
  rfl'

theorem innerPair795RoundedFacts :
    InnerPairRoundedFacts innerPair795Data innerPair795Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair795Input_eq }

noncomputable def innerPair796Data : WideLogData :=
  { lower := endpoint498
    upper := endpoint503 }

noncomputable def innerPair796Input : RationalEnclosure :=
  { lower := (2664353/2097152), upper := (5613175/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair796Input_eq :
    innerPair796Input = outerEnclosure 24 innerPair796Data.output := by
  rfl'

theorem innerPair796RoundedFacts :
    InnerPairRoundedFacts innerPair796Data innerPair796Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair796Input_eq }

noncomputable def innerPair797Data : WideLogData :=
  { lower := endpoint499
    upper := endpoint563 }

noncomputable def innerPair797Input : RationalEnclosure :=
  { lower := (10583503/8388608), upper := (2707595/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair797Input_eq :
    innerPair797Input = outerEnclosure 24 innerPair797Data.output := by
  rfl'

theorem innerPair797RoundedFacts :
    InnerPairRoundedFacts innerPair797Data innerPair797Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair797Input_eq }

noncomputable def innerPair798Data : WideLogData :=
  { lower := endpoint500
    upper := endpoint502 }

noncomputable def innerPair798Input : RationalEnclosure :=
  { lower := (21606609/16777216), upper := (2771923/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair798Input_eq :
    innerPair798Input = outerEnclosure 24 innerPair798Data.output := by
  rfl'

theorem innerPair798RoundedFacts :
    InnerPairRoundedFacts innerPair798Data innerPair798Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair798Input_eq }

noncomputable def innerPair799Data : WideLogData :=
  { lower := endpoint500
    upper := endpoint503 }

noncomputable def innerPair799Input : RationalEnclosure :=
  { lower := (21606609/16777216), upper := (5613175/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair799Input_eq :
    innerPair799Input = outerEnclosure 24 innerPair799Data.output := by
  rfl'

theorem innerPair799RoundedFacts :
    InnerPairRoundedFacts innerPair799Data innerPair799Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair799Input_eq }

noncomputable def innerPair800Data : WideLogData :=
  { lower := endpoint500
    upper := endpoint504 }

noncomputable def innerPair800Input : RationalEnclosure :=
  { lower := (21606609/16777216), upper := (11362753/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair800Input_eq :
    innerPair800Input = outerEnclosure 24 innerPair800Data.output := by
  rfl'

theorem innerPair800RoundedFacts :
    InnerPairRoundedFacts innerPair800Data innerPair800Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair800Input_eq }

noncomputable def innerPair801Data : WideLogData :=
  { lower := endpoint501
    upper := endpoint503 }

noncomputable def innerPair801Input : RationalEnclosure :=
  { lower := (10946703/8388608), upper := (5613175/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair801Input_eq :
    innerPair801Input = outerEnclosure 24 innerPair801Data.output := by
  rfl'

theorem innerPair801RoundedFacts :
    InnerPairRoundedFacts innerPair801Data innerPair801Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair801Input_eq }

noncomputable def innerPair802Data : WideLogData :=
  { lower := endpoint501
    upper := endpoint504 }

noncomputable def innerPair802Input : RationalEnclosure :=
  { lower := (10946703/8388608), upper := (11362753/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair802Input_eq :
    innerPair802Input = outerEnclosure 24 innerPair802Data.output := by
  rfl'

theorem innerPair802RoundedFacts :
    InnerPairRoundedFacts innerPair802Data innerPair802Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair802Input_eq }

noncomputable def innerPair803Data : WideLogData :=
  { lower := endpoint501
    upper := endpoint505 }

noncomputable def innerPair803Input : RationalEnclosure :=
  { lower := (10946703/8388608), upper := (22993947/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair803Input_eq :
    innerPair803Input = outerEnclosure 24 innerPair803Data.output := by
  rfl'

theorem innerPair803RoundedFacts :
    InnerPairRoundedFacts innerPair803Data innerPair803Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair803Input_eq }

noncomputable def innerPair804Data : WideLogData :=
  { lower := endpoint501
    upper := endpoint576 }

noncomputable def innerPair804Input : RationalEnclosure :=
  { lower := (10946703/8388608), upper := (22589657/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair804Input_eq :
    innerPair804Input = outerEnclosure 24 innerPair804Data.output := by
  rfl'

theorem innerPair804RoundedFacts :
    InnerPairRoundedFacts innerPair804Data innerPair804Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair804Input_eq }

noncomputable def innerPair805Data : WideLogData :=
  { lower := endpoint502
    upper := endpoint504 }

noncomputable def innerPair805Input : RationalEnclosure :=
  { lower := (22175383/16777216), upper := (11362753/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair805Input_eq :
    innerPair805Input = outerEnclosure 24 innerPair805Data.output := by
  rfl'

theorem innerPair805RoundedFacts :
    InnerPairRoundedFacts innerPair805Data innerPair805Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair805Input_eq }

noncomputable def innerPair806Data : WideLogData :=
  { lower := endpoint502
    upper := endpoint505 }

noncomputable def innerPair806Input : RationalEnclosure :=
  { lower := (22175383/16777216), upper := (22993947/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair806Input_eq :
    innerPair806Input = outerEnclosure 24 innerPair806Data.output := by
  rfl'

theorem innerPair806RoundedFacts :
    InnerPairRoundedFacts innerPair806Data innerPair806Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair806Input_eq }

noncomputable def innerPair807Data : WideLogData :=
  { lower := endpoint502
    upper := endpoint506 }

noncomputable def innerPair807Input : RationalEnclosure :=
  { lower := (22175383/16777216), upper := (23258161/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair807Input_eq :
    innerPair807Input = outerEnclosure 24 innerPair807Data.output := by
  rfl'

theorem innerPair807RoundedFacts :
    InnerPairRoundedFacts innerPair807Data innerPair807Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair807Input_eq }

noncomputable def innerPair808Data : WideLogData :=
  { lower := endpoint503
    upper := endpoint505 }

noncomputable def innerPair808Input : RationalEnclosure :=
  { lower := (11226349/8388608), upper := (22993947/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair808Input_eq :
    innerPair808Input = outerEnclosure 24 innerPair808Data.output := by
  rfl'

theorem innerPair808RoundedFacts :
    InnerPairRoundedFacts innerPair808Data innerPair808Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair808Input_eq }

noncomputable def innerPair809Data : WideLogData :=
  { lower := endpoint503
    upper := endpoint506 }

noncomputable def innerPair809Input : RationalEnclosure :=
  { lower := (11226349/8388608), upper := (23258161/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair809Input_eq :
    innerPair809Input = outerEnclosure 24 innerPair809Data.output := by
  rfl'

theorem innerPair809RoundedFacts :
    InnerPairRoundedFacts innerPair809Data innerPair809Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair809Input_eq }

noncomputable def innerPair810Data : WideLogData :=
  { lower := endpoint503
    upper := endpoint582 }

noncomputable def innerPair810Input : RationalEnclosure :=
  { lower := (11226349/8388608), upper := (11759139/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair810Input_eq :
    innerPair810Input = outerEnclosure 24 innerPair810Data.output := by
  rfl'

theorem innerPair810RoundedFacts :
    InnerPairRoundedFacts innerPair810Data innerPair810Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair810Input_eq }

noncomputable def innerPair811Data : WideLogData :=
  { lower := endpoint504
    upper := endpoint506 }

noncomputable def innerPair811Input : RationalEnclosure :=
  { lower := (22725505/16777216), upper := (23258161/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair811Input_eq :
    innerPair811Input = outerEnclosure 24 innerPair811Data.output := by
  rfl'

theorem innerPair811RoundedFacts :
    InnerPairRoundedFacts innerPair811Data innerPair811Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair811Input_eq }

noncomputable def innerPair812Data : WideLogData :=
  { lower := endpoint504
    upper := endpoint582 }

noncomputable def innerPair812Input : RationalEnclosure :=
  { lower := (22725505/16777216), upper := (11759139/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair812Input_eq :
    innerPair812Input = outerEnclosure 24 innerPair812Data.output := by
  rfl'

theorem innerPair812RoundedFacts :
    InnerPairRoundedFacts innerPair812Data innerPair812Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair812Input_eq }

noncomputable def innerPair813Data : WideLogData :=
  { lower := endpoint504
    upper := endpoint583 }

noncomputable def innerPair813Input : RationalEnclosure :=
  { lower := (22725505/16777216), upper := (2971803/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair813Input_eq :
    innerPair813Input = outerEnclosure 24 innerPair813Data.output := by
  rfl'

theorem innerPair813RoundedFacts :
    InnerPairRoundedFacts innerPair813Data innerPair813Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair813Input_eq }

noncomputable def innerPair814Data : WideLogData :=
  { lower := endpoint505
    upper := endpoint582 }

noncomputable def innerPair814Input : RationalEnclosure :=
  { lower := (11496973/8388608), upper := (11759139/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair814Input_eq :
    innerPair814Input = outerEnclosure 24 innerPair814Data.output := by
  rfl'

theorem innerPair814RoundedFacts :
    InnerPairRoundedFacts innerPair814Data innerPair814Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair814Input_eq }

noncomputable def innerPair815Data : WideLogData :=
  { lower := endpoint505
    upper := endpoint583 }

noncomputable def innerPair815Input : RationalEnclosure :=
  { lower := (11496973/8388608), upper := (2971803/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair815Input_eq :
    innerPair815Input = outerEnclosure 24 innerPair815Data.output := by
  rfl'

theorem innerPair815RoundedFacts :
    InnerPairRoundedFacts innerPair815Data innerPair815Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair815Input_eq }

noncomputable def innerPair816Data : WideLogData :=
  { lower := endpoint505
    upper := endpoint584 }

noncomputable def innerPair816Input : RationalEnclosure :=
  { lower := (11496973/8388608), upper := (24026717/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair816Input_eq :
    innerPair816Input = outerEnclosure 24 innerPair816Data.output := by
  rfl'

theorem innerPair816RoundedFacts :
    InnerPairRoundedFacts innerPair816Data innerPair816Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair816Input_eq }

noncomputable def innerPair817Data : WideLogData :=
  { lower := endpoint506
    upper := endpoint583 }

noncomputable def innerPair817Input : RationalEnclosure :=
  { lower := (23258159/16777216), upper := (2971803/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair817Input_eq :
    innerPair817Input = outerEnclosure 24 innerPair817Data.output := by
  rfl'

theorem innerPair817RoundedFacts :
    InnerPairRoundedFacts innerPair817Data innerPair817Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair817Input_eq }

noncomputable def innerPair818Data : WideLogData :=
  { lower := endpoint506
    upper := endpoint584 }

noncomputable def innerPair818Input : RationalEnclosure :=
  { lower := (23258159/16777216), upper := (24026717/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair818Input_eq :
    innerPair818Input = outerEnclosure 24 innerPair818Data.output := by
  rfl'

theorem innerPair818RoundedFacts :
    InnerPairRoundedFacts innerPair818Data innerPair818Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair818Input_eq }

noncomputable def innerPair819Data : WideLogData :=
  { lower := endpoint506
    upper := endpoint585 }

noncomputable def innerPair819Input : RationalEnclosure :=
  { lower := (23258159/16777216), upper := (24275273/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair819Input_eq :
    innerPair819Input = outerEnclosure 24 innerPair819Data.output := by
  rfl'

theorem innerPair819RoundedFacts :
    InnerPairRoundedFacts innerPair819Data innerPair819Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair819Input_eq }

noncomputable def innerPair820Data : WideLogData :=
  { lower := endpoint506
    upper := endpoint588 }

noncomputable def innerPair820Input : RationalEnclosure :=
  { lower := (23258159/16777216), upper := (23963999/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair820Input_eq :
    innerPair820Input = outerEnclosure 24 innerPair820Data.output := by
  rfl'

theorem innerPair820RoundedFacts :
    InnerPairRoundedFacts innerPair820Data innerPair820Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair820Input_eq }

noncomputable def innerPair821Data : WideLogData :=
  { lower := endpoint507
    upper := endpoint508 }

noncomputable def innerPair821Input : RationalEnclosure :=
  { lower := (3841563/4194304), upper := (7871133/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair821Input_eq :
    innerPair821Input = outerEnclosure 24 innerPair821Data.output := by
  rfl'

theorem innerPair821RoundedFacts :
    InnerPairRoundedFacts innerPair821Data innerPair821Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair821Input_eq }

noncomputable def innerPair822Data : WideLogData :=
  { lower := endpoint509
    upper := endpoint443 }

noncomputable def innerPair822Input : RationalEnclosure :=
  { lower := (7751685/8388608), upper := (1989309/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair822Input_eq :
    innerPair822Input = outerEnclosure 24 innerPair822Data.output := by
  rfl'

theorem innerPair822RoundedFacts :
    InnerPairRoundedFacts innerPair822Data innerPair822Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair822Input_eq }

noncomputable def innerPair823Data : WideLogData :=
  { lower := endpoint510
    upper := endpoint511 }

noncomputable def innerPair823Input : RationalEnclosure :=
  { lower := (3933963/4194304), upper := (8051881/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair823Input_eq :
    innerPair823Input = outerEnclosure 24 innerPair823Data.output := by
  rfl'

theorem innerPair823RoundedFacts :
    InnerPairRoundedFacts innerPair823Data innerPair823Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair823Input_eq }

noncomputable def innerPair824Data : WideLogData :=
  { lower := endpoint512
    upper := endpoint513 }

noncomputable def innerPair824Input : RationalEnclosure :=
  { lower := (16097485/16777216), upper := (16469915/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair824Input_eq :
    innerPair824Input = outerEnclosure 24 innerPair824Data.output := by
  rfl'

theorem innerPair824RoundedFacts :
    InnerPairRoundedFacts innerPair824Data innerPair824Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair824Input_eq }

noncomputable def innerPair825Data : WideLogData :=
  { lower := endpoint516
    upper := endpoint517 }

noncomputable def innerPair825Input : RationalEnclosure :=
  { lower := (8709319/8388608), upper := (17944041/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair825Input_eq :
    innerPair825Input = outerEnclosure 24 innerPair825Data.output := by
  rfl'

theorem innerPair825RoundedFacts :
    InnerPairRoundedFacts innerPair825Data innerPair825Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair825Input_eq }

noncomputable def innerPair826Data : WideLogData :=
  { lower := endpoint519
    upper := endpoint520 }

noncomputable def innerPair826Input : RationalEnclosure :=
  { lower := (17184969/16777216), upper := (17557295/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair826Input_eq :
    innerPair826Input = outerEnclosure 24 innerPair826Data.output := by
  rfl'

theorem innerPair826RoundedFacts :
    InnerPairRoundedFacts innerPair826Data innerPair826Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair826Input_eq }

noncomputable def innerPair827Data : WideLogData :=
  { lower := endpoint521
    upper := endpoint522 }

noncomputable def innerPair827Input : RationalEnclosure :=
  { lower := (17383795/16777216), upper := (8873047/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair827Input_eq :
    innerPair827Input = outerEnclosure 24 innerPair827Data.output := by
  rfl'

theorem innerPair827RoundedFacts :
    InnerPairRoundedFacts innerPair827Data innerPair827Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair827Input_eq }

noncomputable def innerPair828Data : WideLogData :=
  { lower := endpoint523
    upper := endpoint529 }

noncomputable def innerPair828Input : RationalEnclosure :=
  { lower := (17921535/16777216), upper := (1153343/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair828Input_eq :
    innerPair828Input = outerEnclosure 24 innerPair828Data.output := by
  rfl'

theorem innerPair828RoundedFacts :
    InnerPairRoundedFacts innerPair828Data innerPair828Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair828Input_eq }

noncomputable def innerPair829Data : WideLogData :=
  { lower := endpoint524
    upper := endpoint525 }

noncomputable def innerPair829Input : RationalEnclosure :=
  { lower := (17740403/16777216), upper := (9050367/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair829Input_eq :
    innerPair829Input = outerEnclosure 24 innerPair829Data.output := by
  rfl'

theorem innerPair829RoundedFacts :
    InnerPairRoundedFacts innerPair829Data innerPair829Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair829Input_eq }

noncomputable def innerPair830Data : WideLogData :=
  { lower := endpoint526
    upper := endpoint528 }

noncomputable def innerPair830Input : RationalEnclosure :=
  { lower := (9302757/8388608), upper := (19200213/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair830Input_eq :
    innerPair830Input = outerEnclosure 24 innerPair830Data.output := by
  rfl'

theorem innerPair830RoundedFacts :
    InnerPairRoundedFacts innerPair830Data innerPair830Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair830Input_eq }

noncomputable def innerPair831Data : WideLogData :=
  { lower := endpoint526
    upper := endpoint548 }

noncomputable def innerPair831Input : RationalEnclosure :=
  { lower := (9302757/8388608), upper := (18969089/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair831Input_eq :
    innerPair831Input = outerEnclosure 24 innerPair831Data.output := by
  rfl'

theorem innerPair831RoundedFacts :
    InnerPairRoundedFacts innerPair831Data innerPair831Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair831Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
