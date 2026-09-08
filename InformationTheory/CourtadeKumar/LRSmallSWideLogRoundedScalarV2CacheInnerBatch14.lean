import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
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

noncomputable def innerPair896Data : WideLogData :=
  { lower := endpoint601
    upper := endpoint604 }

noncomputable def innerPair896Input : RationalEnclosure :=
  { lower := (25693909/16777216), upper := (26360643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair896Input_eq :
    innerPair896Input = outerEnclosure 24 innerPair896Data.output := by
  rfl'

theorem innerPair896RoundedFacts :
    InnerPairRoundedFacts innerPair896Data innerPair896Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair896Input_eq }

noncomputable def innerPair897Data : WideLogData :=
  { lower := endpoint602
    upper := endpoint604 }

noncomputable def innerPair897Input : RationalEnclosure :=
  { lower := (12959555/8388608), upper := (26360643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair897Input_eq :
    innerPair897Input = outerEnclosure 24 innerPair897Data.output := by
  rfl'

theorem innerPair897RoundedFacts :
    InnerPairRoundedFacts innerPair897Data innerPair897Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair897Input_eq }

noncomputable def innerPair898Data : WideLogData :=
  { lower := endpoint602
    upper := endpoint605 }

noncomputable def innerPair898Input : RationalEnclosure :=
  { lower := (12959555/8388608), upper := (13288563/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair898Input_eq :
    innerPair898Input = outerEnclosure 24 innerPair898Data.output := by
  rfl'

theorem innerPair898RoundedFacts :
    InnerPairRoundedFacts innerPair898Data innerPair898Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair898Input_eq }

noncomputable def innerPair899Data : WideLogData :=
  { lower := endpoint603
    upper := endpoint605 }

noncomputable def innerPair899Input : RationalEnclosure :=
  { lower := (1633833/1048576), upper := (13288563/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair899Input_eq :
    innerPair899Input = outerEnclosure 24 innerPair899Data.output := by
  rfl'

theorem innerPair899RoundedFacts :
    InnerPairRoundedFacts innerPair899Data innerPair899Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair899Input_eq }

noncomputable def innerPair900Data : WideLogData :=
  { lower := endpoint603
    upper := endpoint606 }

noncomputable def innerPair900Input : RationalEnclosure :=
  { lower := (1633833/1048576), upper := (6697713/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair900Input_eq :
    innerPair900Input = outerEnclosure 24 innerPair900Data.output := by
  rfl'

theorem innerPair900RoundedFacts :
    InnerPairRoundedFacts innerPair900Data innerPair900Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair900Input_eq }

noncomputable def innerPair901Data : WideLogData :=
  { lower := endpoint604
    upper := endpoint606 }

noncomputable def innerPair901Input : RationalEnclosure :=
  { lower := (26360641/16777216), upper := (6697713/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair901Input_eq :
    innerPair901Input = outerEnclosure 24 innerPair901Data.output := by
  rfl'

theorem innerPair901RoundedFacts :
    InnerPairRoundedFacts innerPair901Data innerPair901Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair901Input_eq }

noncomputable def innerPair902Data : WideLogData :=
  { lower := endpoint605
    upper := endpoint607 }

noncomputable def innerPair902Input : RationalEnclosure :=
  { lower := (26577125/16777216), upper := (27001889/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair902Input_eq :
    innerPair902Input = outerEnclosure 24 innerPair902Data.output := by
  rfl'

theorem innerPair902RoundedFacts :
    InnerPairRoundedFacts innerPair902Data innerPair902Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair902Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
