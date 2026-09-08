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

noncomputable def innerPair64Data : WideLogData :=
  { lower := endpoint15
    upper := endpoint16 }

noncomputable def innerPair64Input : RationalEnclosure :=
  { lower := (8778647/16777216), upper := (9388795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair64Input_eq :
    innerPair64Input = outerEnclosure 24 innerPair64Data.output := by
  rfl'

theorem innerPair64RoundedFacts :
    InnerPairRoundedFacts innerPair64Data innerPair64Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair64Input_eq }

noncomputable def innerPair65Data : WideLogData :=
  { lower := endpoint15
    upper := endpoint20 }

noncomputable def innerPair65Input : RationalEnclosure :=
  { lower := (8778647/16777216), upper := (8933277/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair65Input_eq :
    innerPair65Input = outerEnclosure 24 innerPair65Data.output := by
  rfl'

theorem innerPair65RoundedFacts :
    InnerPairRoundedFacts innerPair65Data innerPair65Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair65Input_eq }

noncomputable def innerPair66Data : WideLogData :=
  { lower := endpoint15
    upper := endpoint21 }

noncomputable def innerPair66Input : RationalEnclosure :=
  { lower := (8778647/16777216), upper := (4988765/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair66Input_eq :
    innerPair66Input = outerEnclosure 24 innerPair66Data.output := by
  rfl'

theorem innerPair66RoundedFacts :
    InnerPairRoundedFacts innerPair66Data innerPair66Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair66Input_eq }

noncomputable def innerPair67Data : WideLogData :=
  { lower := endpoint15
    upper := endpoint22 }

noncomputable def innerPair67Input : RationalEnclosure :=
  { lower := (8778647/16777216), upper := (82393/131072) }

set_option maxRecDepth 1000000 in
private theorem innerPair67Input_eq :
    innerPair67Input = outerEnclosure 24 innerPair67Data.output := by
  rfl'

theorem innerPair67RoundedFacts :
    InnerPairRoundedFacts innerPair67Data innerPair67Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair67Input_eq }

noncomputable def innerPair68Data : WideLogData :=
  { lower := endpoint15
    upper := endpoint62 }

noncomputable def innerPair68Input : RationalEnclosure :=
  { lower := (8778647/16777216), upper := (9086495/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair68Input_eq :
    innerPair68Input = outerEnclosure 24 innerPair68Data.output := by
  rfl'

theorem innerPair68RoundedFacts :
    InnerPairRoundedFacts innerPair68Data innerPair68Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair68Input_eq }

noncomputable def innerPair69Data : WideLogData :=
  { lower := endpoint15
    upper := endpoint64 }

noncomputable def innerPair69Input : RationalEnclosure :=
  { lower := (8778647/16777216), upper := (10121541/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair69Input_eq :
    innerPair69Input = outerEnclosure 24 innerPair69Data.output := by
  rfl'

theorem innerPair69RoundedFacts :
    InnerPairRoundedFacts innerPair69Data innerPair69Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair69Input_eq }

noncomputable def innerPair70Data : WideLogData :=
  { lower := endpoint15
    upper := endpoint139 }

noncomputable def innerPair70Input : RationalEnclosure :=
  { lower := (8778647/16777216), upper := (4619163/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair70Input_eq :
    innerPair70Input = outerEnclosure 24 innerPair70Data.output := by
  rfl'

theorem innerPair70RoundedFacts :
    InnerPairRoundedFacts innerPair70Data innerPair70Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair70Input_eq }

noncomputable def innerPair71Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint21 }

noncomputable def innerPair71Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (4988765/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair71Input_eq :
    innerPair71Input = outerEnclosure 24 innerPair71Data.output := by
  rfl'

theorem innerPair71RoundedFacts :
    InnerPairRoundedFacts innerPair71Data innerPair71Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair71Input_eq }

noncomputable def innerPair72Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint22 }

noncomputable def innerPair72Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (82393/131072) }

set_option maxRecDepth 1000000 in
private theorem innerPair72Input_eq :
    innerPair72Input = outerEnclosure 24 innerPair72Data.output := by
  rfl'

theorem innerPair72RoundedFacts :
    InnerPairRoundedFacts innerPair72Data innerPair72Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair72Input_eq }

noncomputable def innerPair73Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint23 }

noncomputable def innerPair73Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (5548213/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair73Input_eq :
    innerPair73Input = outerEnclosure 24 innerPair73Data.output := by
  rfl'

theorem innerPair73RoundedFacts :
    InnerPairRoundedFacts innerPair73Data innerPair73Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair73Input_eq }

noncomputable def innerPair74Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint61 }

noncomputable def innerPair74Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (10264327/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair74Input_eq :
    innerPair74Input = outerEnclosure 24 innerPair74Data.output := by
  rfl'

theorem innerPair74RoundedFacts :
    InnerPairRoundedFacts innerPair74Data innerPair74Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair74Input_eq }

noncomputable def innerPair75Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint63 }

noncomputable def innerPair75Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (9537927/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair75Input_eq :
    innerPair75Input = outerEnclosure 24 innerPair75Data.output := by
  rfl'

theorem innerPair75RoundedFacts :
    InnerPairRoundedFacts innerPair75Data innerPair75Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair75Input_eq }

noncomputable def innerPair76Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint64 }

noncomputable def innerPair76Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (10121541/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair76Input_eq :
    innerPair76Input = outerEnclosure 24 innerPair76Data.output := by
  rfl'

theorem innerPair76RoundedFacts :
    InnerPairRoundedFacts innerPair76Data innerPair76Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair76Input_eq }

noncomputable def innerPair77Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint67 }

noncomputable def innerPair77Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (614517/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair77Input_eq :
    innerPair77Input = outerEnclosure 24 innerPair77Data.output := by
  rfl'

theorem innerPair77RoundedFacts :
    InnerPairRoundedFacts innerPair77Data innerPair77Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair77Input_eq }

noncomputable def innerPair78Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint68 }

noncomputable def innerPair78Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (9685745/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair78Input_eq :
    innerPair78Input = outerEnclosure 24 innerPair78Data.output := by
  rfl'

theorem innerPair78RoundedFacts :
    InnerPairRoundedFacts innerPair78Data innerPair78Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair78Input_eq }

noncomputable def innerPair79Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint182 }

noncomputable def innerPair79Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (1199189/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair79Input_eq :
    innerPair79Input = outerEnclosure 24 innerPair79Data.output := by
  rfl'

theorem innerPair79RoundedFacts :
    InnerPairRoundedFacts innerPair79Data innerPair79Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair79Input_eq }

noncomputable def innerPair80Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint216 }

noncomputable def innerPair80Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (2393751/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair80Input_eq :
    innerPair80Input = outerEnclosure 24 innerPair80Data.output := by
  rfl'

theorem innerPair80RoundedFacts :
    InnerPairRoundedFacts innerPair80Data innerPair80Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair80Input_eq }

noncomputable def innerPair81Data : WideLogData :=
  { lower := endpoint16
    upper := endpoint217 }

noncomputable def innerPair81Input : RationalEnclosure :=
  { lower := (4694397/8388608), upper := (9611999/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair81Input_eq :
    innerPair81Input = outerEnclosure 24 innerPair81Data.output := by
  rfl'

theorem innerPair81RoundedFacts :
    InnerPairRoundedFacts innerPair81Data innerPair81Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair81Input_eq }

noncomputable def innerPair82Data : WideLogData :=
  { lower := endpoint17
    upper := endpoint18 }

noncomputable def innerPair82Input : RationalEnclosure :=
  { lower := (2623585/8388608), upper := (6889731/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair82Input_eq :
    innerPair82Input = outerEnclosure 24 innerPair82Data.output := by
  rfl'

theorem innerPair82RoundedFacts :
    InnerPairRoundedFacts innerPair82Data innerPair82Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair82Input_eq }

noncomputable def innerPair83Data : WideLogData :=
  { lower := endpoint18
    upper := endpoint197 }

noncomputable def innerPair83Input : RationalEnclosure :=
  { lower := (3444865/8388608), upper := (7062693/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair83Input_eq :
    innerPair83Input = outerEnclosure 24 innerPair83Data.output := by
  rfl'

theorem innerPair83RoundedFacts :
    InnerPairRoundedFacts innerPair83Data innerPair83Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair83Input_eq }

noncomputable def innerPair84Data : WideLogData :=
  { lower := endpoint19
    upper := endpoint20 }

noncomputable def innerPair84Input : RationalEnclosure :=
  { lower := (7148509/16777216), upper := (8933277/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair84Input_eq :
    innerPair84Input = outerEnclosure 24 innerPair84Data.output := by
  rfl'

theorem innerPair84RoundedFacts :
    InnerPairRoundedFacts innerPair84Data innerPair84Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair84Input_eq }

noncomputable def innerPair85Data : WideLogData :=
  { lower := endpoint19
    upper := endpoint44 }

noncomputable def innerPair85Input : RationalEnclosure :=
  { lower := (7148509/16777216), upper := (7819689/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair85Input_eq :
    innerPair85Input = outerEnclosure 24 innerPair85Data.output := by
  rfl'

theorem innerPair85RoundedFacts :
    InnerPairRoundedFacts innerPair85Data innerPair85Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair85Input_eq }

noncomputable def innerPair86Data : WideLogData :=
  { lower := endpoint19
    upper := endpoint46 }

noncomputable def innerPair86Input : RationalEnclosure :=
  { lower := (7148509/16777216), upper := (3991685/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair86Input_eq :
    innerPair86Input = outerEnclosure 24 innerPair86Data.output := by
  rfl'

theorem innerPair86RoundedFacts :
    InnerPairRoundedFacts innerPair86Data innerPair86Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair86Input_eq }

noncomputable def innerPair87Data : WideLogData :=
  { lower := endpoint19
    upper := endpoint47 }

noncomputable def innerPair87Input : RationalEnclosure :=
  { lower := (7148509/16777216), upper := (3827197/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair87Input_eq :
    innerPair87Input = outerEnclosure 24 innerPair87Data.output := by
  rfl'

theorem innerPair87RoundedFacts :
    InnerPairRoundedFacts innerPair87Data innerPair87Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair87Input_eq }

noncomputable def innerPair88Data : WideLogData :=
  { lower := endpoint19
    upper := endpoint122 }

noncomputable def innerPair88Input : RationalEnclosure :=
  { lower := (7148509/16777216), upper := (57509/131072) }

set_option maxRecDepth 1000000 in
private theorem innerPair88Input_eq :
    innerPair88Input = outerEnclosure 24 innerPair88Data.output := by
  rfl'

theorem innerPair88RoundedFacts :
    InnerPairRoundedFacts innerPair88Data innerPair88Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair88Input_eq }

noncomputable def innerPair89Data : WideLogData :=
  { lower := endpoint20
    upper := endpoint63 }

noncomputable def innerPair89Input : RationalEnclosure :=
  { lower := (2233319/4194304), upper := (9537927/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair89Input_eq :
    innerPair89Input = outerEnclosure 24 innerPair89Data.output := by
  rfl'

theorem innerPair89RoundedFacts :
    InnerPairRoundedFacts innerPair89Data innerPair89Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair89Input_eq }

noncomputable def innerPair90Data : WideLogData :=
  { lower := endpoint20
    upper := endpoint139 }

noncomputable def innerPair90Input : RationalEnclosure :=
  { lower := (2233319/4194304), upper := (4619163/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair90Input_eq :
    innerPair90Input = outerEnclosure 24 innerPair90Data.output := by
  rfl'

theorem innerPair90RoundedFacts :
    InnerPairRoundedFacts innerPair90Data innerPair90Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair90Input_eq }

noncomputable def innerPair91Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint22 }

noncomputable def innerPair91Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (82393/131072) }

set_option maxRecDepth 1000000 in
private theorem innerPair91Input_eq :
    innerPair91Input = outerEnclosure 24 innerPair91Data.output := by
  rfl'

theorem innerPair91RoundedFacts :
    InnerPairRoundedFacts innerPair91Data innerPair91Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair91Input_eq }

noncomputable def innerPair92Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint23 }

noncomputable def innerPair92Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (5548213/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair92Input_eq :
    innerPair92Input = outerEnclosure 24 innerPair92Data.output := by
  rfl'

theorem innerPair92RoundedFacts :
    InnerPairRoundedFacts innerPair92Data innerPair92Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair92Input_eq }

noncomputable def innerPair93Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint24 }

noncomputable def innerPair93Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (11629081/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair93Input_eq :
    innerPair93Input = outerEnclosure 24 innerPair93Data.output := by
  rfl'

theorem innerPair93RoundedFacts :
    InnerPairRoundedFacts innerPair93Data innerPair93Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair93Input_eq }

noncomputable def innerPair94Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint61 }

noncomputable def innerPair94Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (10264327/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair94Input_eq :
    innerPair94Input = outerEnclosure 24 innerPair94Data.output := by
  rfl'

theorem innerPair94RoundedFacts :
    InnerPairRoundedFacts innerPair94Data innerPair94Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair94Input_eq }

noncomputable def innerPair95Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint64 }

noncomputable def innerPair95Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (10121541/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair95Input_eq :
    innerPair95Input = outerEnclosure 24 innerPair95Data.output := by
  rfl'

theorem innerPair95RoundedFacts :
    InnerPairRoundedFacts innerPair95Data innerPair95Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair95Input_eq }

noncomputable def innerPair96Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint69 }

noncomputable def innerPair96Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (10685535/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair96Input_eq :
    innerPair96Input = outerEnclosure 24 innerPair96Data.output := by
  rfl'

theorem innerPair96RoundedFacts :
    InnerPairRoundedFacts innerPair96Data innerPair96Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair96Input_eq }

noncomputable def innerPair97Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint71 }

noncomputable def innerPair97Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (11231183/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair97Input_eq :
    innerPair97Input = outerEnclosure 24 innerPair97Data.output := by
  rfl'

theorem innerPair97RoundedFacts :
    InnerPairRoundedFacts innerPair97Data innerPair97Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair97Input_eq }

noncomputable def innerPair98Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint189 }

noncomputable def innerPair98Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (5096543/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair98Input_eq :
    innerPair98Input = outerEnclosure 24 innerPair98Data.output := by
  rfl'

theorem innerPair98RoundedFacts :
    InnerPairRoundedFacts innerPair98Data innerPair98Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair98Input_eq }

noncomputable def innerPair99Data : WideLogData :=
  { lower := endpoint21
    upper := endpoint211 }

noncomputable def innerPair99Input : RationalEnclosure :=
  { lower := (9977529/16777216), upper := (2601477/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair99Input_eq :
    innerPair99Input = outerEnclosure 24 innerPair99Data.output := by
  rfl'

theorem innerPair99RoundedFacts :
    InnerPairRoundedFacts innerPair99Data innerPair99Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair99Input_eq }

noncomputable def innerPair100Data : WideLogData :=
  { lower := endpoint22
    upper := endpoint23 }

noncomputable def innerPair100Input : RationalEnclosure :=
  { lower := (10546303/16777216), upper := (5548213/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair100Input_eq :
    innerPair100Input = outerEnclosure 24 innerPair100Data.output := by
  rfl'

theorem innerPair100RoundedFacts :
    InnerPairRoundedFacts innerPair100Data innerPair100Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair100Input_eq }

noncomputable def innerPair101Data : WideLogData :=
  { lower := endpoint22
    upper := endpoint24 }

noncomputable def innerPair101Input : RationalEnclosure :=
  { lower := (10546303/16777216), upper := (11629081/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair101Input_eq :
    innerPair101Input = outerEnclosure 24 innerPair101Data.output := by
  rfl'

theorem innerPair101RoundedFacts :
    InnerPairRoundedFacts innerPair101Data innerPair101Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair101Input_eq }

noncomputable def innerPair102Data : WideLogData :=
  { lower := endpoint22
    upper := endpoint69 }

noncomputable def innerPair102Input : RationalEnclosure :=
  { lower := (10546303/16777216), upper := (10685535/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair102Input_eq :
    innerPair102Input = outerEnclosure 24 innerPair102Data.output := by
  rfl'

theorem innerPair102RoundedFacts :
    InnerPairRoundedFacts innerPair102Data innerPair102Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair102Input_eq }

noncomputable def innerPair103Data : WideLogData :=
  { lower := endpoint22
    upper := endpoint70 }

noncomputable def innerPair103Input : RationalEnclosure :=
  { lower := (10546303/16777216), upper := (2705905/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair103Input_eq :
    innerPair103Input = outerEnclosure 24 innerPair103Data.output := by
  rfl'

theorem innerPair103RoundedFacts :
    InnerPairRoundedFacts innerPair103Data innerPair103Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair103Input_eq }

noncomputable def innerPair104Data : WideLogData :=
  { lower := endpoint22
    upper := endpoint72 }

noncomputable def innerPair104Input : RationalEnclosure :=
  { lower := (10546303/16777216), upper := (189771/262144) }

set_option maxRecDepth 1000000 in
private theorem innerPair104Input_eq :
    innerPair104Input = outerEnclosure 24 innerPair104Data.output := by
  rfl'

theorem innerPair104RoundedFacts :
    InnerPairRoundedFacts innerPair104Data innerPair104Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair104Input_eq }

noncomputable def innerPair105Data : WideLogData :=
  { lower := endpoint22
    upper := endpoint73 }

noncomputable def innerPair105Input : RationalEnclosure :=
  { lower := (10546303/16777216), upper := (12646193/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair105Input_eq :
    innerPair105Input = outerEnclosure 24 innerPair105Data.output := by
  rfl'

theorem innerPair105RoundedFacts :
    InnerPairRoundedFacts innerPair105Data innerPair105Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair105Input_eq }

noncomputable def innerPair106Data : WideLogData :=
  { lower := endpoint22
    upper := endpoint81 }

noncomputable def innerPair106Input : RationalEnclosure :=
  { lower := (10546303/16777216), upper := (10960577/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair106Input_eq :
    innerPair106Input = outerEnclosure 24 innerPair106Data.output := by
  rfl'

theorem innerPair106RoundedFacts :
    InnerPairRoundedFacts innerPair106Data innerPair106Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair106Input_eq }

noncomputable def innerPair107Data : WideLogData :=
  { lower := endpoint22
    upper := endpoint257 }

noncomputable def innerPair107Input : RationalEnclosure :=
  { lower := (10546303/16777216), upper := (10754719/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair107Input_eq :
    innerPair107Input = outerEnclosure 24 innerPair107Data.output := by
  rfl'

theorem innerPair107RoundedFacts :
    InnerPairRoundedFacts innerPair107Data innerPair107Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair107Input_eq }

noncomputable def innerPair108Data : WideLogData :=
  { lower := endpoint23
    upper := endpoint24 }

noncomputable def innerPair108Input : RationalEnclosure :=
  { lower := (11096425/16777216), upper := (11629081/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair108Input_eq :
    innerPair108Input = outerEnclosure 24 innerPair108Data.output := by
  rfl'

theorem innerPair108RoundedFacts :
    InnerPairRoundedFacts innerPair108Data innerPair108Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair108Input_eq }

noncomputable def innerPair109Data : WideLogData :=
  { lower := endpoint23
    upper := endpoint71 }

noncomputable def innerPair109Input : RationalEnclosure :=
  { lower := (11096425/16777216), upper := (11231183/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair109Input_eq :
    innerPair109Input = outerEnclosure 24 innerPair109Data.output := by
  rfl'

theorem innerPair109RoundedFacts :
    InnerPairRoundedFacts innerPair109Data innerPair109Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair109Input_eq }

noncomputable def innerPair110Data : WideLogData :=
  { lower := endpoint23
    upper := endpoint72 }

noncomputable def innerPair110Input : RationalEnclosure :=
  { lower := (11096425/16777216), upper := (189771/262144) }

set_option maxRecDepth 1000000 in
private theorem innerPair110Input_eq :
    innerPair110Input = outerEnclosure 24 innerPair110Data.output := by
  rfl'

theorem innerPair110RoundedFacts :
    InnerPairRoundedFacts innerPair110Data innerPair110Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair110Input_eq }

noncomputable def innerPair111Data : WideLogData :=
  { lower := endpoint23
    upper := endpoint73 }

noncomputable def innerPair111Input : RationalEnclosure :=
  { lower := (11096425/16777216), upper := (12646193/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair111Input_eq :
    innerPair111Input = outerEnclosure 24 innerPair111Data.output := by
  rfl'

theorem innerPair111RoundedFacts :
    InnerPairRoundedFacts innerPair111Data innerPair111Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair111Input_eq }

noncomputable def innerPair112Data : WideLogData :=
  { lower := endpoint23
    upper := endpoint83 }

noncomputable def innerPair112Input : RationalEnclosure :=
  { lower := (11096425/16777216), upper := (5649079/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair112Input_eq :
    innerPair112Input = outerEnclosure 24 innerPair112Data.output := by
  rfl'

theorem innerPair112RoundedFacts :
    InnerPairRoundedFacts innerPair112Data innerPair112Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair112Input_eq }

noncomputable def innerPair113Data : WideLogData :=
  { lower := endpoint23
    upper := endpoint85 }

noncomputable def innerPair113Input : RationalEnclosure :=
  { lower := (11096425/16777216), upper := (11364867/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair113Input_eq :
    innerPair113Input = outerEnclosure 24 innerPair113Data.output := by
  rfl'

theorem innerPair113RoundedFacts :
    InnerPairRoundedFacts innerPair113Data innerPair113Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair113Input_eq }

noncomputable def innerPair114Data : WideLogData :=
  { lower := endpoint23
    upper := endpoint267 }

noncomputable def innerPair114Input : RationalEnclosure :=
  { lower := (11096425/16777216), upper := (5748747/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair114Input_eq :
    innerPair114Input = outerEnclosure 24 innerPair114Data.output := by
  rfl'

theorem innerPair114RoundedFacts :
    InnerPairRoundedFacts innerPair114Data innerPair114Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair114Input_eq }

noncomputable def innerPair115Data : WideLogData :=
  { lower := endpoint23
    upper := endpoint283 }

noncomputable def innerPair115Input : RationalEnclosure :=
  { lower := (11096425/16777216), upper := (11759643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair115Input_eq :
    innerPair115Input = outerEnclosure 24 innerPair115Data.output := by
  rfl'

theorem innerPair115RoundedFacts :
    InnerPairRoundedFacts innerPair115Data innerPair115Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair115Input_eq }

noncomputable def innerPair116Data : WideLogData :=
  { lower := endpoint24
    upper := endpoint72 }

noncomputable def innerPair116Input : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (189771/262144) }

set_option maxRecDepth 1000000 in
private theorem innerPair116Input_eq :
    innerPair116Input = outerEnclosure 24 innerPair116Data.output := by
  rfl'

theorem innerPair116RoundedFacts :
    InnerPairRoundedFacts innerPair116Data innerPair116Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair116Input_eq }

noncomputable def innerPair117Data : WideLogData :=
  { lower := endpoint24
    upper := endpoint73 }

noncomputable def innerPair117Input : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (12646193/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair117Input_eq :
    innerPair117Input = outerEnclosure 24 innerPair117Data.output := by
  rfl'

theorem innerPair117RoundedFacts :
    InnerPairRoundedFacts innerPair117Data innerPair117Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair117Input_eq }

noncomputable def innerPair118Data : WideLogData :=
  { lower := endpoint24
    upper := endpoint74 }

noncomputable def innerPair118Input : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (13132523/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair118Input_eq :
    innerPair118Input = outerEnclosure 24 innerPair118Data.output := by
  rfl'

theorem innerPair118RoundedFacts :
    InnerPairRoundedFacts innerPair118Data innerPair118Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair118Input_eq }

noncomputable def innerPair119Data : WideLogData :=
  { lower := endpoint24
    upper := endpoint82 }

noncomputable def innerPair119Input : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (5944599/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair119Input_eq :
    innerPair119Input = outerEnclosure 24 innerPair119Data.output := by
  rfl'

theorem innerPair119RoundedFacts :
    InnerPairRoundedFacts innerPair119Data innerPair119Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair119Input_eq }

noncomputable def innerPair120Data : WideLogData :=
  { lower := endpoint24
    upper := endpoint86 }

noncomputable def innerPair120Input : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (12271965/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair120Input_eq :
    innerPair120Input = outerEnclosure 24 innerPair120Data.output := by
  rfl'

theorem innerPair120RoundedFacts :
    InnerPairRoundedFacts innerPair120Data innerPair120Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair120Input_eq }

noncomputable def innerPair121Data : WideLogData :=
  { lower := endpoint24
    upper := endpoint87 }

noncomputable def innerPair121Input : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (375555/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair121Input_eq :
    innerPair121Input = outerEnclosure 24 innerPair121Data.output := by
  rfl'

theorem innerPair121RoundedFacts :
    InnerPairRoundedFacts innerPair121Data innerPair121Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair121Input_eq }

noncomputable def innerPair122Data : WideLogData :=
  { lower := endpoint24
    upper := endpoint323 }

noncomputable def innerPair122Input : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (11856903/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair122Input_eq :
    innerPair122Input = outerEnclosure 24 innerPair122Data.output := by
  rfl'

theorem innerPair122RoundedFacts :
    InnerPairRoundedFacts innerPair122Data innerPair122Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair122Input_eq }

noncomputable def innerPair123Data : WideLogData :=
  { lower := endpoint24
    upper := endpoint329 }

noncomputable def innerPair123Input : RationalEnclosure :=
  { lower := (11629079/16777216), upper := (11929479/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair123Input_eq :
    innerPair123Input = outerEnclosure 24 innerPair123Data.output := by
  rfl'

theorem innerPair123RoundedFacts :
    InnerPairRoundedFacts innerPair123Data innerPair123Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair123Input_eq }

noncomputable def innerPair124Data : WideLogData :=
  { lower := endpoint25
    upper := endpoint26 }

noncomputable def innerPair124Input : RationalEnclosure :=
  { lower := (1741421/16777216), upper := (3102483/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair124Input_eq :
    innerPair124Input = outerEnclosure 24 innerPair124Data.output := by
  rfl'

theorem innerPair124RoundedFacts :
    InnerPairRoundedFacts innerPair124Data innerPair124Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair124Input_eq }

noncomputable def innerPair125Data : WideLogData :=
  { lower := endpoint26
    upper := endpoint33 }

noncomputable def innerPair125Input : RationalEnclosure :=
  { lower := (1551241/8388608), upper := (3691217/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair125Input_eq :
    innerPair125Input = outerEnclosure 24 innerPair125Data.output := by
  rfl'

theorem innerPair125RoundedFacts :
    InnerPairRoundedFacts innerPair125Data innerPair125Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair125Input_eq }

noncomputable def innerPair126Data : WideLogData :=
  { lower := endpoint26
    upper := endpoint100 }

noncomputable def innerPair126Input : RationalEnclosure :=
  { lower := (1551241/8388608), upper := (3952143/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair126Input_eq :
    innerPair126Input = outerEnclosure 24 innerPair126Data.output := by
  rfl'

theorem innerPair126RoundedFacts :
    InnerPairRoundedFacts innerPair126Data innerPair126Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair126Input_eq }

noncomputable def innerPair127Data : WideLogData :=
  { lower := endpoint27
    upper := endpoint28 }

noncomputable def innerPair127Input : RationalEnclosure :=
  { lower := (3318965/16777216), upper := (4158001/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair127Input_eq :
    innerPair127Input = outerEnclosure 24 innerPair127Data.output := by
  rfl'

theorem innerPair127RoundedFacts :
    InnerPairRoundedFacts innerPair127Data innerPair127Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair127Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
