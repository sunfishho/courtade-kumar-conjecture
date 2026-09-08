import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2

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

noncomputable def innerPair0Data : WideLogData :=
  { lower := endpoint0
    upper := endpoint1 }

noncomputable def innerPair0Input : RationalEnclosure :=
  { lower := (-1082777/16777216), upper := (247009/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair0Input_eq :
    innerPair0Input = outerEnclosure 24 innerPair0Data.output := by
  rfl'

theorem innerPair0RoundedFacts :
    InnerPairRoundedFacts innerPair0Data innerPair0Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair0Input_eq }

noncomputable def innerPair1Data : WideLogData :=
  { lower := endpoint0
    upper := endpoint2 }

noncomputable def innerPair1Input : RationalEnclosure :=
  { lower := (-1082777/16777216), upper := (1017113/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair1Input_eq :
    innerPair1Input = outerEnclosure 24 innerPair1Data.output := by
  rfl'

theorem innerPair1RoundedFacts :
    InnerPairRoundedFacts innerPair1Data innerPair1Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair1Input_eq }

noncomputable def innerPair2Data : WideLogData :=
  { lower := endpoint1
    upper := endpoint4 }

noncomputable def innerPair2Input : RationalEnclosure :=
  { lower := (1976071/16777216), upper := (2883169/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair2Input_eq :
    innerPair2Input = outerEnclosure 24 innerPair2Data.output := by
  rfl'

theorem innerPair2RoundedFacts :
    InnerPairRoundedFacts innerPair2Data innerPair2Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair2Input_eq }

noncomputable def innerPair3Data : WideLogData :=
  { lower := endpoint1
    upper := endpoint5 }

noncomputable def innerPair3Input : RationalEnclosure :=
  { lower := (1976071/16777216), upper := (233983/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair3Input_eq :
    innerPair3Input = outerEnclosure 24 innerPair3Data.output := by
  rfl'

theorem innerPair3RoundedFacts :
    InnerPairRoundedFacts innerPair3Data innerPair3Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair3Input_eq }

noncomputable def innerPair4Data : WideLogData :=
  { lower := endpoint1
    upper := endpoint6 }

noncomputable def innerPair4Input : RationalEnclosure :=
  { lower := (1976071/16777216), upper := (4562291/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair4Input_eq :
    innerPair4Input = outerEnclosure 24 innerPair4Data.output := by
  rfl'

theorem innerPair4RoundedFacts :
    InnerPairRoundedFacts innerPair4Data innerPair4Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair4Input_eq }

noncomputable def innerPair5Data : WideLogData :=
  { lower := endpoint2
    upper := endpoint1 }

noncomputable def innerPair5Input : RationalEnclosure :=
  { lower := (127139/2097152), upper := (247009/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair5Input_eq :
    innerPair5Input = outerEnclosure 24 innerPair5Data.output := by
  rfl'

theorem innerPair5RoundedFacts :
    InnerPairRoundedFacts innerPair5Data innerPair5Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair5Input_eq }

noncomputable def innerPair6Data : WideLogData :=
  { lower := endpoint2
    upper := endpoint4 }

noncomputable def innerPair6Input : RationalEnclosure :=
  { lower := (127139/2097152), upper := (2883169/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair6Input_eq :
    innerPair6Input = outerEnclosure 24 innerPair6Data.output := by
  rfl'

theorem innerPair6RoundedFacts :
    InnerPairRoundedFacts innerPair6Data innerPair6Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair6Input_eq }

noncomputable def innerPair7Data : WideLogData :=
  { lower := endpoint2
    upper := endpoint5 }

noncomputable def innerPair7Input : RationalEnclosure :=
  { lower := (127139/2097152), upper := (233983/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair7Input_eq :
    innerPair7Input = outerEnclosure 24 innerPair7Data.output := by
  rfl'

theorem innerPair7RoundedFacts :
    InnerPairRoundedFacts innerPair7Data innerPair7Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair7Input_eq }

noncomputable def innerPair8Data : WideLogData :=
  { lower := endpoint2
    upper := endpoint12 }

noncomputable def innerPair8Input : RationalEnclosure :=
  { lower := (127139/2097152), upper := (1217875/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair8Input_eq :
    innerPair8Input = outerEnclosure 24 innerPair8Data.output := by
  rfl'

theorem innerPair8RoundedFacts :
    InnerPairRoundedFacts innerPair8Data innerPair8Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair8Input_eq }

noncomputable def innerPair9Data : WideLogData :=
  { lower := endpoint3
    upper := endpoint1 }

noncomputable def innerPair9Input : RationalEnclosure :=
  { lower := (0), upper := (247009/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair9Input_eq :
    innerPair9Input = outerEnclosure 24 innerPair9Data.output := by
  rfl'

theorem innerPair9RoundedFacts :
    InnerPairRoundedFacts innerPair9Data innerPair9Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair9Input_eq }

noncomputable def innerPair10Data : WideLogData :=
  { lower := endpoint3
    upper := endpoint2 }

noncomputable def innerPair10Input : RationalEnclosure :=
  { lower := (0), upper := (1017113/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair10Input_eq :
    innerPair10Input = outerEnclosure 24 innerPair10Data.output := by
  rfl'

theorem innerPair10RoundedFacts :
    InnerPairRoundedFacts innerPair10Data innerPair10Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair10Input_eq }

noncomputable def innerPair11Data : WideLogData :=
  { lower := endpoint3
    upper := endpoint4 }

noncomputable def innerPair11Input : RationalEnclosure :=
  { lower := (0), upper := (2883169/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair11Input_eq :
    innerPair11Input = outerEnclosure 24 innerPair11Data.output := by
  rfl'

theorem innerPair11RoundedFacts :
    InnerPairRoundedFacts innerPair11Data innerPair11Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair11Input_eq }

noncomputable def innerPair12Data : WideLogData :=
  { lower := endpoint4
    upper := endpoint5 }

noncomputable def innerPair12Input : RationalEnclosure :=
  { lower := (90099/524288), upper := (233983/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair12Input_eq :
    innerPair12Input = outerEnclosure 24 innerPair12Data.output := by
  rfl'

theorem innerPair12RoundedFacts :
    InnerPairRoundedFacts innerPair12Data innerPair12Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair12Input_eq }

noncomputable def innerPair13Data : WideLogData :=
  { lower := endpoint4
    upper := endpoint6 }

noncomputable def innerPair13Input : RationalEnclosure :=
  { lower := (90099/524288), upper := (4562291/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair13Input_eq :
    innerPair13Input = outerEnclosure 24 innerPair13Data.output := by
  rfl'

theorem innerPair13RoundedFacts :
    InnerPairRoundedFacts innerPair13Data innerPair13Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair13Input_eq }

noncomputable def innerPair14Data : WideLogData :=
  { lower := endpoint4
    upper := endpoint7 }

noncomputable def innerPair14Input : RationalEnclosure :=
  { lower := (90099/524288), upper := (333923/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair14Input_eq :
    innerPair14Input = outerEnclosure 24 innerPair14Data.output := by
  rfl'

theorem innerPair14RoundedFacts :
    InnerPairRoundedFacts innerPair14Data innerPair14Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair14Input_eq }

noncomputable def innerPair15Data : WideLogData :=
  { lower := endpoint4
    upper := endpoint116 }

noncomputable def innerPair15Input : RationalEnclosure :=
  { lower := (90099/524288), upper := (3532691/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair15Input_eq :
    innerPair15Input = outerEnclosure 24 innerPair15Data.output := by
  rfl'

theorem innerPair15RoundedFacts :
    InnerPairRoundedFacts innerPair15Data innerPair15Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair15Input_eq }

noncomputable def innerPair16Data : WideLogData :=
  { lower := endpoint5
    upper := endpoint6 }

noncomputable def innerPair16Input : RationalEnclosure :=
  { lower := (3743727/16777216), upper := (4562291/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair16Input_eq :
    innerPair16Input = outerEnclosure 24 innerPair16Data.output := by
  rfl'

theorem innerPair16RoundedFacts :
    InnerPairRoundedFacts innerPair16Data innerPair16Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair16Input_eq }

noncomputable def innerPair17Data : WideLogData :=
  { lower := endpoint5
    upper := endpoint7 }

noncomputable def innerPair17Input : RationalEnclosure :=
  { lower := (3743727/16777216), upper := (333923/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair17Input_eq :
    innerPair17Input = outerEnclosure 24 innerPair17Data.output := by
  rfl'

theorem innerPair17RoundedFacts :
    InnerPairRoundedFacts innerPair17Data innerPair17Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair17Input_eq }

noncomputable def innerPair18Data : WideLogData :=
  { lower := endpoint5
    upper := endpoint9 }

noncomputable def innerPair18Input : RationalEnclosure :=
  { lower := (3743727/16777216), upper := (595105/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair18Input_eq :
    innerPair18Input = outerEnclosure 24 innerPair18Data.output := by
  rfl'

theorem innerPair18RoundedFacts :
    InnerPairRoundedFacts innerPair18Data innerPair18Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair18Input_eq }

noncomputable def innerPair19Data : WideLogData :=
  { lower := endpoint5
    upper := endpoint10 }

noncomputable def innerPair19Input : RationalEnclosure :=
  { lower := (3743727/16777216), upper := (190267/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair19Input_eq :
    innerPair19Input = outerEnclosure 24 innerPair19Data.output := by
  rfl'

theorem innerPair19RoundedFacts :
    InnerPairRoundedFacts innerPair19Data innerPair19Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair19Input_eq }

noncomputable def innerPair20Data : WideLogData :=
  { lower := endpoint5
    upper := endpoint28 }

noncomputable def innerPair20Input : RationalEnclosure :=
  { lower := (3743727/16777216), upper := (4158001/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair20Input_eq :
    innerPair20Input = outerEnclosure 24 innerPair20Data.output := by
  rfl'

theorem innerPair20RoundedFacts :
    InnerPairRoundedFacts innerPair20Data innerPair20Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair20Input_eq }

noncomputable def innerPair21Data : WideLogData :=
  { lower := endpoint6
    upper := endpoint7 }

noncomputable def innerPair21Input : RationalEnclosure :=
  { lower := (2281145/8388608), upper := (333923/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair21Input_eq :
    innerPair21Input = outerEnclosure 24 innerPair21Data.output := by
  rfl'

theorem innerPair21RoundedFacts :
    InnerPairRoundedFacts innerPair21Data innerPair21Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair21Input_eq }

noncomputable def innerPair22Data : WideLogData :=
  { lower := endpoint6
    upper := endpoint10 }

noncomputable def innerPair22Input : RationalEnclosure :=
  { lower := (2281145/8388608), upper := (190267/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair22Input_eq :
    innerPair22Input = outerEnclosure 24 innerPair22Data.output := by
  rfl'

theorem innerPair22RoundedFacts :
    InnerPairRoundedFacts innerPair22Data innerPair22Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair22Input_eq }

noncomputable def innerPair23Data : WideLogData :=
  { lower := endpoint6
    upper := endpoint11 }

noncomputable def innerPair23Input : RationalEnclosure :=
  { lower := (2281145/8388608), upper := (425161/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair23Input_eq :
    innerPair23Input = outerEnclosure 24 innerPair23Data.output := by
  rfl'

theorem innerPair23RoundedFacts :
    InnerPairRoundedFacts innerPair23Data innerPair23Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair23Input_eq }

noncomputable def innerPair24Data : WideLogData :=
  { lower := endpoint6
    upper := endpoint34 }

noncomputable def innerPair24Input : RationalEnclosure :=
  { lower := (2281145/8388608), upper := (5532343/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair24Input_eq :
    innerPair24Input = outerEnclosure 24 innerPair24Data.output := by
  rfl'

theorem innerPair24RoundedFacts :
    InnerPairRoundedFacts innerPair24Data innerPair24Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair24Input_eq }

noncomputable def innerPair25Data : WideLogData :=
  { lower := endpoint6
    upper := endpoint37 }

noncomputable def innerPair25Input : RationalEnclosure :=
  { lower := (2281145/8388608), upper := (4957067/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair25Input_eq :
    innerPair25Input = outerEnclosure 24 innerPair25Data.output := by
  rfl'

theorem innerPair25RoundedFacts :
    InnerPairRoundedFacts innerPair25Data innerPair25Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair25Input_eq }

noncomputable def innerPair26Data : WideLogData :=
  { lower := endpoint7
    upper := endpoint10 }

noncomputable def innerPair26Input : RationalEnclosure :=
  { lower := (5342767/16777216), upper := (190267/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair26Input_eq :
    innerPair26Input = outerEnclosure 24 innerPair26Data.output := by
  rfl'

theorem innerPair26RoundedFacts :
    InnerPairRoundedFacts innerPair26Data innerPair26Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair26Input_eq }

noncomputable def innerPair27Data : WideLogData :=
  { lower := endpoint7
    upper := endpoint11 }

noncomputable def innerPair27Input : RationalEnclosure :=
  { lower := (5342767/16777216), upper := (425161/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair27Input_eq :
    innerPair27Input = outerEnclosure 24 innerPair27Data.output := by
  rfl'

theorem innerPair27RoundedFacts :
    InnerPairRoundedFacts innerPair27Data innerPair27Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair27Input_eq }

noncomputable def innerPair28Data : WideLogData :=
  { lower := endpoint7
    upper := endpoint13 }

noncomputable def innerPair28Input : RationalEnclosure :=
  { lower := (5342767/16777216), upper := (233983/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair28Input_eq :
    innerPair28Input = outerEnclosure 24 innerPair28Data.output := by
  rfl'

theorem innerPair28RoundedFacts :
    InnerPairRoundedFacts innerPair28Data innerPair28Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair28Input_eq }

noncomputable def innerPair29Data : WideLogData :=
  { lower := endpoint7
    upper := endpoint38 }

noncomputable def innerPair29Input : RationalEnclosure :=
  { lower := (5342767/16777216), upper := (5719799/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair29Input_eq :
    innerPair29Input = outerEnclosure 24 innerPair29Data.output := by
  rfl'

theorem innerPair29RoundedFacts :
    InnerPairRoundedFacts innerPair29Data innerPair29Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair29Input_eq }

noncomputable def innerPair30Data : WideLogData :=
  { lower := endpoint7
    upper := endpoint119 }

noncomputable def innerPair30Input : RationalEnclosure :=
  { lower := (5342767/16777216), upper := (5905185/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair30Input_eq :
    innerPair30Input = outerEnclosure 24 innerPair30Data.output := by
  rfl'

theorem innerPair30RoundedFacts :
    InnerPairRoundedFacts innerPair30Data innerPair30Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair30Input_eq }

noncomputable def innerPair31Data : WideLogData :=
  { lower := endpoint8
    upper := endpoint9 }

noncomputable def innerPair31Input : RationalEnclosure :=
  { lower := (1330475/8388608), upper := (595105/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair31Input_eq :
    innerPair31Input = outerEnclosure 24 innerPair31Data.output := by
  rfl'

theorem innerPair31RoundedFacts :
    InnerPairRoundedFacts innerPair31Data innerPair31Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair31Input_eq }

noncomputable def innerPair32Data : WideLogData :=
  { lower := endpoint8
    upper := endpoint27 }

noncomputable def innerPair32Input : RationalEnclosure :=
  { lower := (1330475/8388608), upper := (1659483/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair32Input_eq :
    innerPair32Input = outerEnclosure 24 innerPair32Data.output := by
  rfl'

theorem innerPair32RoundedFacts :
    InnerPairRoundedFacts innerPair32Data innerPair32Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair32Input_eq }

noncomputable def innerPair33Data : WideLogData :=
  { lower := endpoint9
    upper := endpoint34 }

noncomputable def innerPair33Input : RationalEnclosure :=
  { lower := (4760839/16777216), upper := (5532343/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair33Input_eq :
    innerPair33Input = outerEnclosure 24 innerPair33Data.output := by
  rfl'

theorem innerPair33RoundedFacts :
    InnerPairRoundedFacts innerPair33Data innerPair33Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair33Input_eq }

noncomputable def innerPair34Data : WideLogData :=
  { lower := endpoint10
    upper := endpoint11 }

noncomputable def innerPair34Input : RationalEnclosure :=
  { lower := (6088543/16777216), upper := (425161/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair34Input_eq :
    innerPair34Input = outerEnclosure 24 innerPair34Data.output := by
  rfl'

theorem innerPair34RoundedFacts :
    InnerPairRoundedFacts innerPair34Data innerPair34Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair34Input_eq }

noncomputable def innerPair35Data : WideLogData :=
  { lower := endpoint10
    upper := endpoint13 }

noncomputable def innerPair35Input : RationalEnclosure :=
  { lower := (6088543/16777216), upper := (233983/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair35Input_eq :
    innerPair35Input = outerEnclosure 24 innerPair35Data.output := by
  rfl'

theorem innerPair35RoundedFacts :
    InnerPairRoundedFacts innerPair35Data innerPair35Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair35Input_eq }

noncomputable def innerPair36Data : WideLogData :=
  { lower := endpoint10
    upper := endpoint14 }

noncomputable def innerPair36Input : RationalEnclosure :=
  { lower := (6088543/16777216), upper := (4072735/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair36Input_eq :
    innerPair36Input = outerEnclosure 24 innerPair36Data.output := by
  rfl'

theorem innerPair36RoundedFacts :
    InnerPairRoundedFacts innerPair36Data innerPair36Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair36Input_eq }

noncomputable def innerPair37Data : WideLogData :=
  { lower := endpoint10
    upper := endpoint42 }

noncomputable def innerPair37Input : RationalEnclosure :=
  { lower := (6088543/16777216), upper := (6449359/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair37Input_eq :
    innerPair37Input = outerEnclosure 24 innerPair37Data.output := by
  rfl'

theorem innerPair37RoundedFacts :
    InnerPairRoundedFacts innerPair37Data innerPair37Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair37Input_eq }

noncomputable def innerPair38Data : WideLogData :=
  { lower := endpoint10
    upper := endpoint120 }

noncomputable def innerPair38Input : RationalEnclosure :=
  { lower := (6088543/16777216), upper := (6626897/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair38Input_eq :
    innerPair38Input = outerEnclosure 24 innerPair38Data.output := by
  rfl'

theorem innerPair38RoundedFacts :
    InnerPairRoundedFacts innerPair38Data innerPair38Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair38Input_eq }

noncomputable def innerPair39Data : WideLogData :=
  { lower := endpoint10
    upper := endpoint160 }

noncomputable def innerPair39Input : RationalEnclosure :=
  { lower := (6088543/16777216), upper := (794985/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair39Input_eq :
    innerPair39Input = outerEnclosure 24 innerPair39Data.output := by
  rfl'

theorem innerPair39RoundedFacts :
    InnerPairRoundedFacts innerPair39Data innerPair39Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair39Input_eq }

noncomputable def innerPair40Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint13 }

noncomputable def innerPair40Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (233983/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair40Input_eq :
    innerPair40Input = outerEnclosure 24 innerPair40Data.output := by
  rfl'

theorem innerPair40RoundedFacts :
    InnerPairRoundedFacts innerPair40Data innerPair40Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair40Input_eq }

noncomputable def innerPair41Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint14 }

noncomputable def innerPair41Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (4072735/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair41Input_eq :
    innerPair41Input = outerEnclosure 24 innerPair41Data.output := by
  rfl'

theorem innerPair41RoundedFacts :
    InnerPairRoundedFacts innerPair41Data innerPair41Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair41Input_eq }

noncomputable def innerPair42Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint15 }

noncomputable def innerPair42Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (1097331/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair42Input_eq :
    innerPair42Input = outerEnclosure 24 innerPair42Data.output := by
  rfl'

theorem innerPair42RoundedFacts :
    InnerPairRoundedFacts innerPair42Data innerPair42Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair42Input_eq }

noncomputable def innerPair43Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint16 }

noncomputable def innerPair43Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (9388795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair43Input_eq :
    innerPair43Input = outerEnclosure 24 innerPair43Data.output := by
  rfl'

theorem innerPair43RoundedFacts :
    InnerPairRoundedFacts innerPair43Data innerPair43Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair43Input_eq }

noncomputable def innerPair44Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint19 }

noncomputable def innerPair44Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (3574255/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair44Input_eq :
    innerPair44Input = outerEnclosure 24 innerPair44Data.output := by
  rfl'

theorem innerPair44RoundedFacts :
    InnerPairRoundedFacts innerPair44Data innerPair44Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair44Input_eq }

noncomputable def innerPair45Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint43 }

noncomputable def innerPair45Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (7318839/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair45Input_eq :
    innerPair45Input = outerEnclosure 24 innerPair45Data.output := by
  rfl'

theorem innerPair45RoundedFacts :
    InnerPairRoundedFacts innerPair45Data innerPair45Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair45Input_eq }

noncomputable def innerPair46Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint44 }

noncomputable def innerPair46Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (7819689/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair46Input_eq :
    innerPair46Input = outerEnclosure 24 innerPair46Data.output := by
  rfl'

theorem innerPair46RoundedFacts :
    InnerPairRoundedFacts innerPair46Data innerPair46Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair46Input_eq }

noncomputable def innerPair47Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint49 }

noncomputable def innerPair47Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (6976435/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair47Input_eq :
    innerPair47Input = outerEnclosure 24 innerPair47Data.output := by
  rfl'

theorem innerPair47RoundedFacts :
    InnerPairRoundedFacts innerPair47Data innerPair47Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair47Input_eq }

noncomputable def innerPair48Data : WideLogData :=
  { lower := endpoint11
    upper := endpoint121 }

noncomputable def innerPair48Input : RationalEnclosure :=
  { lower := (6802575/16777216), upper := (1754905/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair48Input_eq :
    innerPair48Input = outerEnclosure 24 innerPair48Data.output := by
  rfl'

theorem innerPair48RoundedFacts :
    InnerPairRoundedFacts innerPair48Data innerPair48Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair48Input_eq }

noncomputable def innerPair49Data : WideLogData :=
  { lower := endpoint12
    upper := endpoint26 }

noncomputable def innerPair49Input : RationalEnclosure :=
  { lower := (2435749/16777216), upper := (3102483/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair49Input_eq :
    innerPair49Input = outerEnclosure 24 innerPair49Data.output := by
  rfl'

theorem innerPair49RoundedFacts :
    InnerPairRoundedFacts innerPair49Data innerPair49Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair49Input_eq }

noncomputable def innerPair50Data : WideLogData :=
  { lower := endpoint13
    upper := endpoint14 }

noncomputable def innerPair50Input : RationalEnclosure :=
  { lower := (7487455/16777216), upper := (4072735/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair50Input_eq :
    innerPair50Input = outerEnclosure 24 innerPair50Data.output := by
  rfl'

theorem innerPair50RoundedFacts :
    InnerPairRoundedFacts innerPair50Data innerPair50Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair50Input_eq }

noncomputable def innerPair51Data : WideLogData :=
  { lower := endpoint13
    upper := endpoint15 }

noncomputable def innerPair51Input : RationalEnclosure :=
  { lower := (7487455/16777216), upper := (1097331/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair51Input_eq :
    innerPair51Input = outerEnclosure 24 innerPair51Data.output := by
  rfl'

theorem innerPair51RoundedFacts :
    InnerPairRoundedFacts innerPair51Data innerPair51Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair51Input_eq }

noncomputable def innerPair52Data : WideLogData :=
  { lower := endpoint13
    upper := endpoint16 }

noncomputable def innerPair52Input : RationalEnclosure :=
  { lower := (7487455/16777216), upper := (9388795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair52Input_eq :
    innerPair52Input = outerEnclosure 24 innerPair52Data.output := by
  rfl'

theorem innerPair52RoundedFacts :
    InnerPairRoundedFacts innerPair52Data innerPair52Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair52Input_eq }

noncomputable def innerPair53Data : WideLogData :=
  { lower := endpoint13
    upper := endpoint21 }

noncomputable def innerPair53Input : RationalEnclosure :=
  { lower := (7487455/16777216), upper := (4988765/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair53Input_eq :
    innerPair53Input = outerEnclosure 24 innerPair53Data.output := by
  rfl'

theorem innerPair53RoundedFacts :
    InnerPairRoundedFacts innerPair53Data innerPair53Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair53Input_eq }

noncomputable def innerPair54Data : WideLogData :=
  { lower := endpoint13
    upper := endpoint44 }

noncomputable def innerPair54Input : RationalEnclosure :=
  { lower := (7487455/16777216), upper := (7819689/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair54Input_eq :
    innerPair54Input = outerEnclosure 24 innerPair54Data.output := by
  rfl'

theorem innerPair54RoundedFacts :
    InnerPairRoundedFacts innerPair54Data innerPair54Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair54Input_eq }

noncomputable def innerPair55Data : WideLogData :=
  { lower := endpoint13
    upper := endpoint46 }

noncomputable def innerPair55Input : RationalEnclosure :=
  { lower := (7487455/16777216), upper := (3991685/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair55Input_eq :
    innerPair55Input = outerEnclosure 24 innerPair55Data.output := by
  rfl'

theorem innerPair55RoundedFacts :
    InnerPairRoundedFacts innerPair55Data innerPair55Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair55Input_eq }

noncomputable def innerPair56Data : WideLogData :=
  { lower := endpoint14
    upper := endpoint15 }

noncomputable def innerPair56Input : RationalEnclosure :=
  { lower := (8145469/16777216), upper := (1097331/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair56Input_eq :
    innerPair56Input = outerEnclosure 24 innerPair56Data.output := by
  rfl'

theorem innerPair56RoundedFacts :
    InnerPairRoundedFacts innerPair56Data innerPair56Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair56Input_eq }

noncomputable def innerPair57Data : WideLogData :=
  { lower := endpoint14
    upper := endpoint16 }

noncomputable def innerPair57Input : RationalEnclosure :=
  { lower := (8145469/16777216), upper := (9388795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair57Input_eq :
    innerPair57Input = outerEnclosure 24 innerPair57Data.output := by
  rfl'

theorem innerPair57RoundedFacts :
    InnerPairRoundedFacts innerPair57Data innerPair57Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair57Input_eq }

noncomputable def innerPair58Data : WideLogData :=
  { lower := endpoint14
    upper := endpoint20 }

noncomputable def innerPair58Input : RationalEnclosure :=
  { lower := (8145469/16777216), upper := (8933277/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair58Input_eq :
    innerPair58Input = outerEnclosure 24 innerPair58Data.output := by
  rfl'

theorem innerPair58RoundedFacts :
    InnerPairRoundedFacts innerPair58Data innerPair58Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair58Input_eq }

noncomputable def innerPair59Data : WideLogData :=
  { lower := endpoint14
    upper := endpoint21 }

noncomputable def innerPair59Input : RationalEnclosure :=
  { lower := (8145469/16777216), upper := (4988765/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair59Input_eq :
    innerPair59Input = outerEnclosure 24 innerPair59Data.output := by
  rfl'

theorem innerPair59RoundedFacts :
    InnerPairRoundedFacts innerPair59Data innerPair59Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair59Input_eq }

noncomputable def innerPair60Data : WideLogData :=
  { lower := endpoint14
    upper := endpoint22 }

noncomputable def innerPair60Input : RationalEnclosure :=
  { lower := (8145469/16777216), upper := (82393/131072) }

set_option maxRecDepth 1000000 in
private theorem innerPair60Input_eq :
    innerPair60Input = outerEnclosure 24 innerPair60Data.output := by
  rfl'

theorem innerPair60RoundedFacts :
    InnerPairRoundedFacts innerPair60Data innerPair60Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair60Input_eq }

noncomputable def innerPair61Data : WideLogData :=
  { lower := endpoint14
    upper := endpoint48 }

noncomputable def innerPair61Input : RationalEnclosure :=
  { lower := (8145469/16777216), upper := (4232523/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair61Input_eq :
    innerPair61Input = outerEnclosure 24 innerPair61Data.output := by
  rfl'

theorem innerPair61RoundedFacts :
    InnerPairRoundedFacts innerPair61Data innerPair61Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair61Input_eq }

noncomputable def innerPair62Data : WideLogData :=
  { lower := endpoint14
    upper := endpoint133 }

noncomputable def innerPair62Input : RationalEnclosure :=
  { lower := (8145469/16777216), upper := (8622579/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair62Input_eq :
    innerPair62Input = outerEnclosure 24 innerPair62Data.output := by
  rfl'

theorem innerPair62RoundedFacts :
    InnerPairRoundedFacts innerPair62Data innerPair62Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair62Input_eq }

noncomputable def innerPair63Data : WideLogData :=
  { lower := endpoint14
    upper := endpoint134 }

noncomputable def innerPair63Input : RationalEnclosure :=
  { lower := (8145469/16777216), upper := (1063071/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair63Input_eq :
    innerPair63Input = outerEnclosure 24 innerPair63Data.output := by
  rfl'

theorem innerPair63RoundedFacts :
    InnerPairRoundedFacts innerPair63Data innerPair63Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair63Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
