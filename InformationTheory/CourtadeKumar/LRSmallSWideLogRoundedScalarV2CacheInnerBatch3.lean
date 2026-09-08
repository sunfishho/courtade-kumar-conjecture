import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5

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

noncomputable def innerPair192Data : WideLogData :=
  { lower := endpoint56
    upper := endpoint175 }

noncomputable def innerPair192Input : RationalEnclosure :=
  { lower := (2165433/4194304), upper := (9010061/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair192Input_eq :
    innerPair192Input = outerEnclosure 24 innerPair192Data.output := by
  rfl'

theorem innerPair192RoundedFacts :
    InnerPairRoundedFacts innerPair192Data innerPair192Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair192Input_eq }

noncomputable def innerPair193Data : WideLogData :=
  { lower := endpoint57
    upper := endpoint58 }

noncomputable def innerPair193Input : RationalEnclosure :=
  { lower := (3971299/8388608), upper := (4369883/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair193Input_eq :
    innerPair193Input = outerEnclosure 24 innerPair193Data.output := by
  rfl'

theorem innerPair193RoundedFacts :
    InnerPairRoundedFacts innerPair193Data innerPair193Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair193Input_eq }

noncomputable def innerPair194Data : WideLogData :=
  { lower := endpoint57
    upper := endpoint126 }

noncomputable def innerPair194Input : RationalEnclosure :=
  { lower := (3971299/8388608), upper := (8185751/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair194Input_eq :
    innerPair194Input = outerEnclosure 24 innerPair194Data.output := by
  rfl'

theorem innerPair194RoundedFacts :
    InnerPairRoundedFacts innerPair194Data innerPair194Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair194Input_eq }

noncomputable def innerPair195Data : WideLogData :=
  { lower := endpoint57
    upper := endpoint132 }

noncomputable def innerPair195Input : RationalEnclosure :=
  { lower := (3971299/8388608), upper := (8266025/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair195Input_eq :
    innerPair195Input = outerEnclosure 24 innerPair195Data.output := by
  rfl'

theorem innerPair195RoundedFacts :
    InnerPairRoundedFacts innerPair195Data innerPair195Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair195Input_eq }

noncomputable def innerPair196Data : WideLogData :=
  { lower := endpoint58
    upper := endpoint136 }

noncomputable def innerPair196Input : RationalEnclosure :=
  { lower := (8739765/16777216), upper := (8971713/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair196Input_eq :
    innerPair196Input = outerEnclosure 24 innerPair196Data.output := by
  rfl'

theorem innerPair196RoundedFacts :
    InnerPairRoundedFacts innerPair196Data innerPair196Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair196Input_eq }

noncomputable def innerPair197Data : WideLogData :=
  { lower := endpoint59
    upper := endpoint60 }

noncomputable def innerPair197Input : RationalEnclosure :=
  { lower := (4350397/8388608), upper := (296899/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair197Input_eq :
    innerPair197Input = outerEnclosure 24 innerPair197Data.output := by
  rfl'

theorem innerPair197RoundedFacts :
    InnerPairRoundedFacts innerPair197Data innerPair197Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair197Input_eq }

noncomputable def innerPair198Data : WideLogData :=
  { lower := endpoint60
    upper := endpoint183 }

noncomputable def innerPair198Input : RationalEnclosure :=
  { lower := (9500767/16777216), upper := (9722497/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair198Input_eq :
    innerPair198Input = outerEnclosure 24 innerPair198Data.output := by
  rfl'

theorem innerPair198RoundedFacts :
    InnerPairRoundedFacts innerPair198Data innerPair198Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair198Input_eq }

noncomputable def innerPair199Data : WideLogData :=
  { lower := endpoint61
    upper := endpoint69 }

noncomputable def innerPair199Input : RationalEnclosure :=
  { lower := (5132163/8388608), upper := (10685535/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair199Input_eq :
    innerPair199Input = outerEnclosure 24 innerPair199Data.output := by
  rfl'

theorem innerPair199RoundedFacts :
    InnerPairRoundedFacts innerPair199Data innerPair199Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair199Input_eq }

noncomputable def innerPair200Data : WideLogData :=
  { lower := endpoint61
    upper := endpoint70 }

noncomputable def innerPair200Input : RationalEnclosure :=
  { lower := (5132163/8388608), upper := (2705905/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair200Input_eq :
    innerPair200Input = outerEnclosure 24 innerPair200Data.output := by
  rfl'

theorem innerPair200RoundedFacts :
    InnerPairRoundedFacts innerPair200Data innerPair200Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair200Input_eq }

noncomputable def innerPair201Data : WideLogData :=
  { lower := endpoint61
    upper := endpoint81 }

noncomputable def innerPair201Input : RationalEnclosure :=
  { lower := (5132163/8388608), upper := (10960577/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair201Input_eq :
    innerPair201Input = outerEnclosure 24 innerPair201Data.output := by
  rfl'

theorem innerPair201RoundedFacts :
    InnerPairRoundedFacts innerPair201Data innerPair201Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair201Input_eq }

noncomputable def innerPair202Data : WideLogData :=
  { lower := endpoint61
    upper := endpoint241 }

noncomputable def innerPair202Input : RationalEnclosure :=
  { lower := (5132163/8388608), upper := (10441117/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair202Input_eq :
    innerPair202Input = outerEnclosure 24 innerPair202Data.output := by
  rfl'

theorem innerPair202RoundedFacts :
    InnerPairRoundedFacts innerPair202Data innerPair202Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair202Input_eq }

noncomputable def innerPair203Data : WideLogData :=
  { lower := endpoint61
    upper := endpoint251 }

noncomputable def innerPair203Input : RationalEnclosure :=
  { lower := (5132163/8388608), upper := (10476253/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair203Input_eq :
    innerPair203Input = outerEnclosure 24 innerPair203Data.output := by
  rfl'

theorem innerPair203RoundedFacts :
    InnerPairRoundedFacts innerPair203Data innerPair203Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair203Input_eq }

noncomputable def innerPair204Data : WideLogData :=
  { lower := endpoint62
    upper := endpoint63 }

noncomputable def innerPair204Input : RationalEnclosure :=
  { lower := (4543247/8388608), upper := (9537927/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair204Input_eq :
    innerPair204Input = outerEnclosure 24 innerPair204Data.output := by
  rfl'

theorem innerPair204RoundedFacts :
    InnerPairRoundedFacts innerPair204Data innerPair204Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair204Input_eq }

noncomputable def innerPair205Data : WideLogData :=
  { lower := endpoint62
    upper := endpoint67 }

noncomputable def innerPair205Input : RationalEnclosure :=
  { lower := (4543247/8388608), upper := (614517/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair205Input_eq :
    innerPair205Input = outerEnclosure 24 innerPair205Data.output := by
  rfl'

theorem innerPair205RoundedFacts :
    InnerPairRoundedFacts innerPair205Data innerPair205Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair205Input_eq }

noncomputable def innerPair206Data : WideLogData :=
  { lower := endpoint62
    upper := endpoint178 }

noncomputable def innerPair206Input : RationalEnclosure :=
  { lower := (4543247/8388608), upper := (9426203/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair206Input_eq :
    innerPair206Input = outerEnclosure 24 innerPair206Data.output := by
  rfl'

theorem innerPair206RoundedFacts :
    InnerPairRoundedFacts innerPair206Data innerPair206Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair206Input_eq }

noncomputable def innerPair207Data : WideLogData :=
  { lower := endpoint62
    upper := endpoint214 }

noncomputable def innerPair207Input : RationalEnclosure :=
  { lower := (4543247/8388608), upper := (9313729/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair207Input_eq :
    innerPair207Input = outerEnclosure 24 innerPair207Data.output := by
  rfl'

theorem innerPair207RoundedFacts :
    InnerPairRoundedFacts innerPair207Data innerPair207Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair207Input_eq }

noncomputable def innerPair208Data : WideLogData :=
  { lower := endpoint63
    upper := endpoint64 }

noncomputable def innerPair208Input : RationalEnclosure :=
  { lower := (4768963/8388608), upper := (10121541/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair208Input_eq :
    innerPair208Input = outerEnclosure 24 innerPair208Data.output := by
  rfl'

theorem innerPair208RoundedFacts :
    InnerPairRoundedFacts innerPair208Data innerPair208Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair208Input_eq }

noncomputable def innerPair209Data : WideLogData :=
  { lower := endpoint63
    upper := endpoint67 }

noncomputable def innerPair209Input : RationalEnclosure :=
  { lower := (4768963/8388608), upper := (614517/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair209Input_eq :
    innerPair209Input = outerEnclosure 24 innerPair209Data.output := by
  rfl'

theorem innerPair209RoundedFacts :
    InnerPairRoundedFacts innerPair209Data innerPair209Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair209Input_eq }

noncomputable def innerPair210Data : WideLogData :=
  { lower := endpoint63
    upper := endpoint183 }

noncomputable def innerPair210Input : RationalEnclosure :=
  { lower := (4768963/8388608), upper := (9722497/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair210Input_eq :
    innerPair210Input = outerEnclosure 24 innerPair210Data.output := by
  rfl'

theorem innerPair210RoundedFacts :
    InnerPairRoundedFacts innerPair210Data innerPair210Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair210Input_eq }

noncomputable def innerPair211Data : WideLogData :=
  { lower := endpoint63
    upper := endpoint184 }

noncomputable def innerPair211Input : RationalEnclosure :=
  { lower := (4768963/8388608), upper := (612235/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair211Input_eq :
    innerPair211Input = outerEnclosure 24 innerPair211Data.output := by
  rfl'

theorem innerPair211RoundedFacts :
    InnerPairRoundedFacts innerPair211Data innerPair211Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair211Input_eq }

noncomputable def innerPair212Data : WideLogData :=
  { lower := endpoint63
    upper := endpoint218 }

noncomputable def innerPair212Input : RationalEnclosure :=
  { lower := (4768963/8388608), upper := (152487/262144) }

set_option maxRecDepth 1000000 in
private theorem innerPair212Input_eq :
    innerPair212Input = outerEnclosure 24 innerPair212Data.output := by
  rfl'

theorem innerPair212RoundedFacts :
    InnerPairRoundedFacts innerPair212Data innerPair212Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair212Input_eq }

noncomputable def innerPair213Data : WideLogData :=
  { lower := endpoint64
    upper := endpoint69 }

noncomputable def innerPair213Input : RationalEnclosure :=
  { lower := (2530385/4194304), upper := (10685535/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair213Input_eq :
    innerPair213Input = outerEnclosure 24 innerPair213Data.output := by
  rfl'

theorem innerPair213RoundedFacts :
    InnerPairRoundedFacts innerPair213Data innerPair213Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair213Input_eq }

noncomputable def innerPair214Data : WideLogData :=
  { lower := endpoint64
    upper := endpoint211 }

noncomputable def innerPair214Input : RationalEnclosure :=
  { lower := (2530385/4194304), upper := (2601477/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair214Input_eq :
    innerPair214Input = outerEnclosure 24 innerPair214Data.output := by
  rfl'

theorem innerPair214RoundedFacts :
    InnerPairRoundedFacts innerPair214Data innerPair214Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair214Input_eq }

noncomputable def innerPair215Data : WideLogData :=
  { lower := endpoint64
    upper := endpoint223 }

noncomputable def innerPair215Input : RationalEnclosure :=
  { lower := (2530385/4194304), upper := (5149917/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair215Input_eq :
    innerPair215Input = outerEnclosure 24 innerPair215Data.output := by
  rfl'

theorem innerPair215RoundedFacts :
    InnerPairRoundedFacts innerPair215Data innerPair215Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair215Input_eq }

noncomputable def innerPair216Data : WideLogData :=
  { lower := endpoint64
    upper := endpoint252 }

noncomputable def innerPair216Input : RationalEnclosure :=
  { lower := (2530385/4194304), upper := (41469/65536) }

set_option maxRecDepth 1000000 in
private theorem innerPair216Input_eq :
    innerPair216Input = outerEnclosure 24 innerPair216Data.output := by
  rfl'

theorem innerPair216RoundedFacts :
    InnerPairRoundedFacts innerPair216Data innerPair216Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair216Input_eq }

noncomputable def innerPair217Data : WideLogData :=
  { lower := endpoint65
    upper := endpoint66 }

noncomputable def innerPair217Input : RationalEnclosure :=
  { lower := (277961/524288), upper := (9463527/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair217Input_eq :
    innerPair217Input = outerEnclosure 24 innerPair217Data.output := by
  rfl'

theorem innerPair217RoundedFacts :
    InnerPairRoundedFacts innerPair217Data innerPair217Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair217Input_eq }

noncomputable def innerPair218Data : WideLogData :=
  { lower := endpoint65
    upper := endpoint179 }

noncomputable def innerPair218Input : RationalEnclosure :=
  { lower := (277961/524288), upper := (4562291/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair218Input_eq :
    innerPair218Input = outerEnclosure 24 innerPair218Data.output := by
  rfl'

theorem innerPair218RoundedFacts :
    InnerPairRoundedFacts innerPair218Data innerPair218Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair218Input_eq }

noncomputable def innerPair219Data : WideLogData :=
  { lower := endpoint66
    upper := endpoint183 }

noncomputable def innerPair219Input : RationalEnclosure :=
  { lower := (4731763/8388608), upper := (9722497/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair219Input_eq :
    innerPair219Input = outerEnclosure 24 innerPair219Data.output := by
  rfl'

theorem innerPair219RoundedFacts :
    InnerPairRoundedFacts innerPair219Data innerPair219Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair219Input_eq }

noncomputable def innerPair220Data : WideLogData :=
  { lower := endpoint67
    upper := endpoint61 }

noncomputable def innerPair220Input : RationalEnclosure :=
  { lower := (9832271/16777216), upper := (10264327/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair220Input_eq :
    innerPair220Input = outerEnclosure 24 innerPair220Data.output := by
  rfl'

theorem innerPair220RoundedFacts :
    InnerPairRoundedFacts innerPair220Data innerPair220Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair220Input_eq }

noncomputable def innerPair221Data : WideLogData :=
  { lower := endpoint67
    upper := endpoint64 }

noncomputable def innerPair221Input : RationalEnclosure :=
  { lower := (9832271/16777216), upper := (10121541/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair221Input_eq :
    innerPair221Input = outerEnclosure 24 innerPair221Data.output := by
  rfl'

theorem innerPair221RoundedFacts :
    InnerPairRoundedFacts innerPair221Data innerPair221Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair221Input_eq }

noncomputable def innerPair222Data : WideLogData :=
  { lower := endpoint67
    upper := endpoint70 }

noncomputable def innerPair222Input : RationalEnclosure :=
  { lower := (9832271/16777216), upper := (2705905/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair222Input_eq :
    innerPair222Input = outerEnclosure 24 innerPair222Data.output := by
  rfl'

theorem innerPair222RoundedFacts :
    InnerPairRoundedFacts innerPair222Data innerPair222Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair222Input_eq }

noncomputable def innerPair223Data : WideLogData :=
  { lower := endpoint67
    upper := endpoint211 }

noncomputable def innerPair223Input : RationalEnclosure :=
  { lower := (9832271/16777216), upper := (2601477/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair223Input_eq :
    innerPair223Input = outerEnclosure 24 innerPair223Data.output := by
  rfl'

theorem innerPair223RoundedFacts :
    InnerPairRoundedFacts innerPair223Data innerPair223Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair223Input_eq }

noncomputable def innerPair224Data : WideLogData :=
  { lower := endpoint67
    upper := endpoint220 }

noncomputable def innerPair224Input : RationalEnclosure :=
  { lower := (9832271/16777216), upper := (5024845/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair224Input_eq :
    innerPair224Input = outerEnclosure 24 innerPair224Data.output := by
  rfl'

theorem innerPair224RoundedFacts :
    InnerPairRoundedFacts innerPair224Data innerPair224Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair224Input_eq }

noncomputable def innerPair225Data : WideLogData :=
  { lower := endpoint68
    upper := endpoint61 }

noncomputable def innerPair225Input : RationalEnclosure :=
  { lower := (605359/1048576), upper := (10264327/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair225Input_eq :
    innerPair225Input = outerEnclosure 24 innerPair225Data.output := by
  rfl'

theorem innerPair225RoundedFacts :
    InnerPairRoundedFacts innerPair225Data innerPair225Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair225Input_eq }

noncomputable def innerPair226Data : WideLogData :=
  { lower := endpoint68
    upper := endpoint64 }

noncomputable def innerPair226Input : RationalEnclosure :=
  { lower := (605359/1048576), upper := (10121541/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair226Input_eq :
    innerPair226Input = outerEnclosure 24 innerPair226Data.output := by
  rfl'

theorem innerPair226RoundedFacts :
    InnerPairRoundedFacts innerPair226Data innerPair226Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair226Input_eq }

noncomputable def innerPair227Data : WideLogData :=
  { lower := endpoint68
    upper := endpoint185 }

noncomputable def innerPair227Input : RationalEnclosure :=
  { lower := (605359/1048576), upper := (4952529/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair227Input_eq :
    innerPair227Input = outerEnclosure 24 innerPair227Data.output := by
  rfl'

theorem innerPair227RoundedFacts :
    InnerPairRoundedFacts innerPair227Data innerPair227Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair227Input_eq }

noncomputable def innerPair228Data : WideLogData :=
  { lower := endpoint69
    upper := endpoint71 }

noncomputable def innerPair228Input : RationalEnclosure :=
  { lower := (5342767/8388608), upper := (11231183/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair228Input_eq :
    innerPair228Input = outerEnclosure 24 innerPair228Data.output := by
  rfl'

theorem innerPair228RoundedFacts :
    InnerPairRoundedFacts innerPair228Data innerPair228Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair228Input_eq }

noncomputable def innerPair229Data : WideLogData :=
  { lower := endpoint69
    upper := endpoint81 }

noncomputable def innerPair229Input : RationalEnclosure :=
  { lower := (5342767/8388608), upper := (10960577/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair229Input_eq :
    innerPair229Input = outerEnclosure 24 innerPair229Data.output := by
  rfl'

theorem innerPair229RoundedFacts :
    InnerPairRoundedFacts innerPair229Data innerPair229Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair229Input_eq }

noncomputable def innerPair230Data : WideLogData :=
  { lower := endpoint69
    upper := endpoint85 }

noncomputable def innerPair230Input : RationalEnclosure :=
  { lower := (5342767/8388608), upper := (11364867/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair230Input_eq :
    innerPair230Input = outerEnclosure 24 innerPair230Data.output := by
  rfl'

theorem innerPair230RoundedFacts :
    InnerPairRoundedFacts innerPair230Data innerPair230Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair230Input_eq }

noncomputable def innerPair231Data : WideLogData :=
  { lower := endpoint69
    upper := endpoint258 }

noncomputable def innerPair231Input : RationalEnclosure :=
  { lower := (5342767/8388608), upper := (5446119/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair231Input_eq :
    innerPair231Input = outerEnclosure 24 innerPair231Data.output := by
  rfl'

theorem innerPair231RoundedFacts :
    InnerPairRoundedFacts innerPair231Data innerPair231Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair231Input_eq }

noncomputable def innerPair232Data : WideLogData :=
  { lower := endpoint69
    upper := endpoint287 }

noncomputable def innerPair232Input : RationalEnclosure :=
  { lower := (5342767/8388608), upper := (11147087/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair232Input_eq :
    innerPair232Input = outerEnclosure 24 innerPair232Data.output := by
  rfl'

theorem innerPair232RoundedFacts :
    InnerPairRoundedFacts innerPair232Data innerPair232Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair232Input_eq }

noncomputable def innerPair233Data : WideLogData :=
  { lower := endpoint70
    upper := endpoint71 }

noncomputable def innerPair233Input : RationalEnclosure :=
  { lower := (5411809/8388608), upper := (11231183/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair233Input_eq :
    innerPair233Input = outerEnclosure 24 innerPair233Data.output := by
  rfl'

theorem innerPair233RoundedFacts :
    InnerPairRoundedFacts innerPair233Data innerPair233Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair233Input_eq }

noncomputable def innerPair234Data : WideLogData :=
  { lower := endpoint70
    upper := endpoint85 }

noncomputable def innerPair234Input : RationalEnclosure :=
  { lower := (5411809/8388608), upper := (11364867/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair234Input_eq :
    innerPair234Input = outerEnclosure 24 innerPair234Data.output := by
  rfl'

theorem innerPair234RoundedFacts :
    InnerPairRoundedFacts innerPair234Data innerPair234Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair234Input_eq }

noncomputable def innerPair235Data : WideLogData :=
  { lower := endpoint70
    upper := endpoint265 }

noncomputable def innerPair235Input : RationalEnclosure :=
  { lower := (5411809/8388608), upper := (11062567/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair235Input_eq :
    innerPair235Input = outerEnclosure 24 innerPair235Data.output := by
  rfl'

theorem innerPair235RoundedFacts :
    InnerPairRoundedFacts innerPair235Data innerPair235Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair235Input_eq }

noncomputable def innerPair236Data : WideLogData :=
  { lower := endpoint70
    upper := endpoint267 }

noncomputable def innerPair236Input : RationalEnclosure :=
  { lower := (5411809/8388608), upper := (5748747/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair236Input_eq :
    innerPair236Input = outerEnclosure 24 innerPair236Data.output := by
  rfl'

theorem innerPair236RoundedFacts :
    InnerPairRoundedFacts innerPair236Data innerPair236Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair236Input_eq }

noncomputable def innerPair237Data : WideLogData :=
  { lower := endpoint71
    upper := endpoint82 }

noncomputable def innerPair237Input : RationalEnclosure :=
  { lower := (5615591/8388608), upper := (5944599/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair237Input_eq :
    innerPair237Input = outerEnclosure 24 innerPair237Data.output := by
  rfl'

theorem innerPair237RoundedFacts :
    InnerPairRoundedFacts innerPair237Data innerPair237Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair237Input_eq }

noncomputable def innerPair238Data : WideLogData :=
  { lower := endpoint71
    upper := endpoint267 }

noncomputable def innerPair238Input : RationalEnclosure :=
  { lower := (5615591/8388608), upper := (5748747/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair238Input_eq :
    innerPair238Input = outerEnclosure 24 innerPair238Data.output := by
  rfl'

theorem innerPair238RoundedFacts :
    InnerPairRoundedFacts innerPair238Data innerPair238Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair238Input_eq }

noncomputable def innerPair239Data : WideLogData :=
  { lower := endpoint71
    upper := endpoint275 }

noncomputable def innerPair239Input : RationalEnclosure :=
  { lower := (5615591/8388608), upper := (714457/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair239Input_eq :
    innerPair239Input = outerEnclosure 24 innerPair239Data.output := by
  rfl'

theorem innerPair239RoundedFacts :
    InnerPairRoundedFacts innerPair239Data innerPair239Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair239Input_eq }

noncomputable def innerPair240Data : WideLogData :=
  { lower := endpoint71
    upper := endpoint278 }

noncomputable def innerPair240Input : RationalEnclosure :=
  { lower := (5615591/8388608), upper := (1445427/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair240Input_eq :
    innerPair240Input = outerEnclosure 24 innerPair240Data.output := by
  rfl'

theorem innerPair240RoundedFacts :
    InnerPairRoundedFacts innerPair240Data innerPair240Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair240Input_eq }

noncomputable def innerPair241Data : WideLogData :=
  { lower := endpoint71
    upper := endpoint283 }

noncomputable def innerPair241Input : RationalEnclosure :=
  { lower := (5615591/8388608), upper := (11759643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair241Input_eq :
    innerPair241Input = outerEnclosure 24 innerPair241Data.output := by
  rfl'

theorem innerPair241RoundedFacts :
    InnerPairRoundedFacts innerPair241Data innerPair241Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair241Input_eq }

noncomputable def innerPair242Data : WideLogData :=
  { lower := endpoint72
    upper := endpoint73 }

noncomputable def innerPair242Input : RationalEnclosure :=
  { lower := (6072671/8388608), upper := (12646193/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair242Input_eq :
    innerPair242Input = outerEnclosure 24 innerPair242Data.output := by
  rfl'

theorem innerPair242RoundedFacts :
    InnerPairRoundedFacts innerPair242Data innerPair242Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair242Input_eq }

noncomputable def innerPair243Data : WideLogData :=
  { lower := endpoint72
    upper := endpoint74 }

noncomputable def innerPair243Input : RationalEnclosure :=
  { lower := (6072671/8388608), upper := (13132523/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair243Input_eq :
    innerPair243Input = outerEnclosure 24 innerPair243Data.output := by
  rfl'

theorem innerPair243RoundedFacts :
    InnerPairRoundedFacts innerPair243Data innerPair243Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair243Input_eq }

noncomputable def innerPair244Data : WideLogData :=
  { lower := endpoint72
    upper := endpoint75 }

noncomputable def innerPair244Input : RationalEnclosure :=
  { lower := (6072671/8388608), upper := (425161/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair244Input_eq :
    innerPair244Input = outerEnclosure 24 innerPair244Data.output := by
  rfl'

theorem innerPair244RoundedFacts :
    InnerPairRoundedFacts innerPair244Data innerPair244Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair244Input_eq }

noncomputable def innerPair245Data : WideLogData :=
  { lower := endpoint72
    upper := endpoint76 }

noncomputable def innerPair245Input : RationalEnclosure :=
  { lower := (6072671/8388608), upper := (14064831/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair245Input_eq :
    innerPair245Input = outerEnclosure 24 innerPair245Data.output := by
  rfl'

theorem innerPair245RoundedFacts :
    InnerPairRoundedFacts innerPair245Data innerPair245Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair245Input_eq }

noncomputable def innerPair246Data : WideLogData :=
  { lower := endpoint72
    upper := endpoint80 }

noncomputable def innerPair246Input : RationalEnclosure :=
  { lower := (6072671/8388608), upper := (6685251/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair246Input_eq :
    innerPair246Input = outerEnclosure 24 innerPair246Data.output := by
  rfl'

theorem innerPair246RoundedFacts :
    InnerPairRoundedFacts innerPair246Data innerPair246Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair246Input_eq }

noncomputable def innerPair247Data : WideLogData :=
  { lower := endpoint72
    upper := endpoint89 }

noncomputable def innerPair247Input : RationalEnclosure :=
  { lower := (6072671/8388608), upper := (12522375/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair247Input_eq :
    innerPair247Input = outerEnclosure 24 innerPair247Data.output := by
  rfl'

theorem innerPair247RoundedFacts :
    InnerPairRoundedFacts innerPair247Data innerPair247Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair247Input_eq }

noncomputable def innerPair248Data : WideLogData :=
  { lower := endpoint72
    upper := endpoint284 }

noncomputable def innerPair248Input : RationalEnclosure :=
  { lower := (6072671/8388608), upper := (12397637/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair248Input_eq :
    innerPair248Input = outerEnclosure 24 innerPair248Data.output := by
  rfl'

theorem innerPair248RoundedFacts :
    InnerPairRoundedFacts innerPair248Data innerPair248Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair248Input_eq }

noncomputable def innerPair249Data : WideLogData :=
  { lower := endpoint73
    upper := endpoint74 }

noncomputable def innerPair249Input : RationalEnclosure :=
  { lower := (790387/1048576), upper := (13132523/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair249Input_eq :
    innerPair249Input = outerEnclosure 24 innerPair249Data.output := by
  rfl'

theorem innerPair249RoundedFacts :
    InnerPairRoundedFacts innerPair249Data innerPair249Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair249Input_eq }

noncomputable def innerPair250Data : WideLogData :=
  { lower := endpoint73
    upper := endpoint75 }

noncomputable def innerPair250Input : RationalEnclosure :=
  { lower := (790387/1048576), upper := (425161/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair250Input_eq :
    innerPair250Input = outerEnclosure 24 innerPair250Data.output := by
  rfl'

theorem innerPair250RoundedFacts :
    InnerPairRoundedFacts innerPair250Data innerPair250Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair250Input_eq }

noncomputable def innerPair251Data : WideLogData :=
  { lower := endpoint73
    upper := endpoint76 }

noncomputable def innerPair251Input : RationalEnclosure :=
  { lower := (790387/1048576), upper := (14064831/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair251Input_eq :
    innerPair251Input = outerEnclosure 24 innerPair251Data.output := by
  rfl'

theorem innerPair251RoundedFacts :
    InnerPairRoundedFacts innerPair251Data innerPair251Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair251Input_eq }

noncomputable def innerPair252Data : WideLogData :=
  { lower := endpoint73
    upper := endpoint77 }

noncomputable def innerPair252Input : RationalEnclosure :=
  { lower := (790387/1048576), upper := (7256125/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair252Input_eq :
    innerPair252Input = outerEnclosure 24 innerPair252Data.output := by
  rfl'

theorem innerPair252RoundedFacts :
    InnerPairRoundedFacts innerPair252Data innerPair252Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair252Input_eq }

noncomputable def innerPair253Data : WideLogData :=
  { lower := endpoint73
    upper := endpoint88 }

noncomputable def innerPair253Input : RationalEnclosure :=
  { lower := (790387/1048576), upper := (805695/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair253Input_eq :
    innerPair253Input = outerEnclosure 24 innerPair253Data.output := by
  rfl'

theorem innerPair253RoundedFacts :
    InnerPairRoundedFacts innerPair253Data innerPair253Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair253Input_eq }

noncomputable def innerPair254Data : WideLogData :=
  { lower := endpoint73
    upper := endpoint291 }

noncomputable def innerPair254Input : RationalEnclosure :=
  { lower := (790387/1048576), upper := (13251935/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair254Input_eq :
    innerPair254Input = outerEnclosure 24 innerPair254Data.output := by
  rfl'

theorem innerPair254RoundedFacts :
    InnerPairRoundedFacts innerPair254Data innerPair254Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair254Input_eq }

noncomputable def innerPair255Data : WideLogData :=
  { lower := endpoint73
    upper := endpoint337 }

noncomputable def innerPair255Input : RationalEnclosure :=
  { lower := (790387/1048576), upper := (406633/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair255Input_eq :
    innerPair255Input = outerEnclosure 24 innerPair255Data.output := by
  rfl'

theorem innerPair255RoundedFacts :
    InnerPairRoundedFacts innerPair255Data innerPair255Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair255Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
