import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3
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

noncomputable def innerPair384Data : WideLogData :=
  { lower := endpoint99
    upper := endpoint492 }

noncomputable def innerPair384Input : RationalEnclosure :=
  { lower := (18431655/16777216), upper := (19283475/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair384Input_eq :
    innerPair384Input = outerEnclosure 24 innerPair384Data.output := by
  rfl'

theorem innerPair384RoundedFacts :
    InnerPairRoundedFacts innerPair384Data innerPair384Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair384Input_eq }

noncomputable def innerPair385Data : WideLogData :=
  { lower := endpoint99
    upper := endpoint527 }

noncomputable def innerPair385Input : RationalEnclosure :=
  { lower := (18431655/16777216), upper := (18862971/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair385Input_eq :
    innerPair385Input = outerEnclosure 24 innerPair385Data.output := by
  rfl'

theorem innerPair385RoundedFacts :
    InnerPairRoundedFacts innerPair385Data innerPair385Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair385Input_eq }

noncomputable def innerPair386Data : WideLogData :=
  { lower := endpoint99
    upper := endpoint530 }

noncomputable def innerPair386Input : RationalEnclosure :=
  { lower := (18431655/16777216), upper := (18947919/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair386Input_eq :
    innerPair386Input = outerEnclosure 24 innerPair386Data.output := by
  rfl'

theorem innerPair386RoundedFacts :
    InnerPairRoundedFacts innerPair386Data innerPair386Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair386Input_eq }

noncomputable def innerPair387Data : WideLogData :=
  { lower := endpoint99
    upper := endpoint547 }

noncomputable def innerPair387Input : RationalEnclosure :=
  { lower := (18431655/16777216), upper := (18820335/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair387Input_eq :
    innerPair387Input = outerEnclosure 24 innerPair387Data.output := by
  rfl'

theorem innerPair387RoundedFacts :
    InnerPairRoundedFacts innerPair387Data innerPair387Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair387Input_eq }

noncomputable def innerPair388Data : WideLogData :=
  { lower := endpoint100
    upper := endpoint28 }

noncomputable def innerPair388Input : RationalEnclosure :=
  { lower := (1976071/8388608), upper := (4158001/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair388Input_eq :
    innerPair388Input = outerEnclosure 24 innerPair388Data.output := by
  rfl'

theorem innerPair388RoundedFacts :
    InnerPairRoundedFacts innerPair388Data innerPair388Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair388Input_eq }

noncomputable def innerPair389Data : WideLogData :=
  { lower := endpoint100
    upper := endpoint29 }

noncomputable def innerPair389Input : RationalEnclosure :=
  { lower := (1976071/8388608), upper := (1090341/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair389Input_eq :
    innerPair389Input = outerEnclosure 24 innerPair389Data.output := by
  rfl'

theorem innerPair389RoundedFacts :
    InnerPairRoundedFacts innerPair389Data innerPair389Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair389Input_eq }

noncomputable def innerPair390Data : WideLogData :=
  { lower := endpoint100
    upper := endpoint115 }

noncomputable def innerPair390Input : RationalEnclosure :=
  { lower := (1976071/8388608), upper := (4323421/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair390Input_eq :
    innerPair390Input = outerEnclosure 24 innerPair390Data.output := by
  rfl'

theorem innerPair390RoundedFacts :
    InnerPairRoundedFacts innerPair390Data innerPair390Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair390Input_eq }

noncomputable def innerPair391Data : WideLogData :=
  { lower := endpoint101
    upper := endpoint102 }

noncomputable def innerPair391Input : RationalEnclosure :=
  { lower := (2772427/16777216), upper := (3372653/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair391Input_eq :
    innerPair391Input = outerEnclosure 24 innerPair391Data.output := by
  rfl'

theorem innerPair391RoundedFacts :
    InnerPairRoundedFacts innerPair391Data innerPair391Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair391Input_eq }

noncomputable def innerPair392Data : WideLogData :=
  { lower := endpoint103
    upper := endpoint104 }

noncomputable def innerPair392Input : RationalEnclosure :=
  { lower := (37579/131072), upper := (5199167/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair392Input_eq :
    innerPair392Input = outerEnclosure 24 innerPair392Data.output := by
  rfl'

theorem innerPair392RoundedFacts :
    InnerPairRoundedFacts innerPair392Data innerPair392Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair392Input_eq }

noncomputable def innerPair393Data : WideLogData :=
  { lower := endpoint105
    upper := endpoint106 }

noncomputable def innerPair393Input : RationalEnclosure :=
  { lower := (2355711/8388608), upper := (2551373/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair393Input_eq :
    innerPair393Input = outerEnclosure 24 innerPair393Data.output := by
  rfl'

theorem innerPair393RoundedFacts :
    InnerPairRoundedFacts innerPair393Data innerPair393Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair393Input_eq }

noncomputable def innerPair394Data : WideLogData :=
  { lower := endpoint107
    upper := endpoint108 }

noncomputable def innerPair394Input : RationalEnclosure :=
  { lower := (5766337/16777216), upper := (6314961/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair394Input_eq :
    innerPair394Input = outerEnclosure 24 innerPair394Data.output := by
  rfl'

theorem innerPair394RoundedFacts :
    InnerPairRoundedFacts innerPair394Data innerPair394Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair394Input_eq }

noncomputable def innerPair395Data : WideLogData :=
  { lower := endpoint107
    upper := endpoint109 }

noncomputable def innerPair395Input : RationalEnclosure :=
  { lower := (5766337/16777216), upper := (6134073/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair395Input_eq :
    innerPair395Input = outerEnclosure 24 innerPair395Data.output := by
  rfl'

theorem innerPair395RoundedFacts :
    InnerPairRoundedFacts innerPair395Data innerPair395Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair395Input_eq }

noncomputable def innerPair396Data : WideLogData :=
  { lower := endpoint107
    upper := endpoint155 }

noncomputable def innerPair396Input : RationalEnclosure :=
  { lower := (5766337/16777216), upper := (1510723/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair396Input_eq :
    innerPair396Input = outerEnclosure 24 innerPair396Data.output := by
  rfl'

theorem innerPair396RoundedFacts :
    InnerPairRoundedFacts innerPair396Data innerPair396Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair396Input_eq }

noncomputable def innerPair397Data : WideLogData :=
  { lower := endpoint109
    upper := endpoint110 }

noncomputable def innerPair397Input : RationalEnclosure :=
  { lower := (766759/2097152), upper := (6714967/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair397Input_eq :
    innerPair397Input = outerEnclosure 24 innerPair397Data.output := by
  rfl'

theorem innerPair397RoundedFacts :
    InnerPairRoundedFacts innerPair397Data innerPair397Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair397Input_eq }

noncomputable def innerPair398Data : WideLogData :=
  { lower := endpoint111
    upper := endpoint112 }

noncomputable def innerPair398Input : RationalEnclosure :=
  { lower := (6582687/16777216), upper := (7105657/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair398Input_eq :
    innerPair398Input = outerEnclosure 24 innerPair398Data.output := by
  rfl'

theorem innerPair398RoundedFacts :
    InnerPairRoundedFacts innerPair398Data innerPair398Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair398Input_eq }

noncomputable def innerPair399Data : WideLogData :=
  { lower := endpoint111
    upper := endpoint123 }

noncomputable def innerPair399Input : RationalEnclosure :=
  { lower := (6582687/16777216), upper := (3423105/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair399Input_eq :
    innerPair399Input = outerEnclosure 24 innerPair399Data.output := by
  rfl'

theorem innerPair399RoundedFacts :
    InnerPairRoundedFacts innerPair399Data innerPair399Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair399Input_eq }

noncomputable def innerPair400Data : WideLogData :=
  { lower := endpoint112
    upper := endpoint125 }

noncomputable def innerPair400Input : RationalEnclosure :=
  { lower := (888207/2097152), upper := (7424423/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair400Input_eq :
    innerPair400Input = outerEnclosure 24 innerPair400Data.output := by
  rfl'

theorem innerPair400RoundedFacts :
    InnerPairRoundedFacts innerPair400Data innerPair400Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair400Input_eq }

noncomputable def innerPair401Data : WideLogData :=
  { lower := endpoint113
    upper := endpoint114 }

noncomputable def innerPair401Input : RationalEnclosure :=
  { lower := (3701679/8388608), upper := (7901729/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair401Input_eq :
    innerPair401Input = outerEnclosure 24 innerPair401Data.output := by
  rfl'

theorem innerPair401RoundedFacts :
    InnerPairRoundedFacts innerPair401Data innerPair401Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair401Input_eq }

noncomputable def innerPair402Data : WideLogData :=
  { lower := endpoint116
    upper := endpoint100 }

noncomputable def innerPair402Input : RationalEnclosure :=
  { lower := (1766345/8388608), upper := (3952143/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair402Input_eq :
    innerPair402Input = outerEnclosure 24 innerPair402Data.output := by
  rfl'

theorem innerPair402RoundedFacts :
    InnerPairRoundedFacts innerPair402Data innerPair402Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair402Input_eq }

noncomputable def innerPair403Data : WideLogData :=
  { lower := endpoint116
    upper := endpoint154 }

noncomputable def innerPair403Input : RationalEnclosure :=
  { lower := (1766345/8388608), upper := (3848259/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair403Input_eq :
    innerPair403Input = outerEnclosure 24 innerPair403Data.output := by
  rfl'

theorem innerPair403RoundedFacts :
    InnerPairRoundedFacts innerPair403Data innerPair403Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair403Input_eq }

noncomputable def innerPair404Data : WideLogData :=
  { lower := endpoint117
    upper := endpoint118 }

noncomputable def innerPair404Input : RationalEnclosure :=
  { lower := (3585699/16777216), upper := (4003845/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair404Input_eq :
    innerPair404Input = outerEnclosure 24 innerPair404Data.output := by
  rfl'

theorem innerPair404RoundedFacts :
    InnerPairRoundedFacts innerPair404Data innerPair404Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair404Input_eq }

noncomputable def innerPair405Data : WideLogData :=
  { lower := endpoint119
    upper := endpoint41 }

noncomputable def innerPair405Input : RationalEnclosure :=
  { lower := (184537/524288), upper := (6269921/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair405Input_eq :
    innerPair405Input = outerEnclosure 24 innerPair405Data.output := by
  rfl'

theorem innerPair405RoundedFacts :
    InnerPairRoundedFacts innerPair405Data innerPair405Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair405Input_eq }

noncomputable def innerPair406Data : WideLogData :=
  { lower := endpoint119
    upper := endpoint42 }

noncomputable def innerPair406Input : RationalEnclosure :=
  { lower := (184537/524288), upper := (6449359/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair406Input_eq :
    innerPair406Input = outerEnclosure 24 innerPair406Data.output := by
  rfl'

theorem innerPair406RoundedFacts :
    InnerPairRoundedFacts innerPair406Data innerPair406Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair406Input_eq }

noncomputable def innerPair407Data : WideLogData :=
  { lower := endpoint120
    upper := endpoint18 }

noncomputable def innerPair407Input : RationalEnclosure :=
  { lower := (414181/1048576), upper := (6889731/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair407Input_eq :
    innerPair407Input = outerEnclosure 24 innerPair407Data.output := by
  rfl'

theorem innerPair407RoundedFacts :
    InnerPairRoundedFacts innerPair407Data innerPair407Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair407Input_eq }

noncomputable def innerPair408Data : WideLogData :=
  { lower := endpoint120
    upper := endpoint19 }

noncomputable def innerPair408Input : RationalEnclosure :=
  { lower := (414181/1048576), upper := (3574255/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair408Input_eq :
    innerPair408Input = outerEnclosure 24 innerPair408Data.output := by
  rfl'

theorem innerPair408RoundedFacts :
    InnerPairRoundedFacts innerPair408Data innerPair408Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair408Input_eq }

noncomputable def innerPair409Data : WideLogData :=
  { lower := endpoint120
    upper := endpoint49 }

noncomputable def innerPair409Input : RationalEnclosure :=
  { lower := (414181/1048576), upper := (6976435/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair409Input_eq :
    innerPair409Input = outerEnclosure 24 innerPair409Data.output := by
  rfl'

theorem innerPair409RoundedFacts :
    InnerPairRoundedFacts innerPair409Data innerPair409Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair409Input_eq }

noncomputable def innerPair410Data : WideLogData :=
  { lower := endpoint121
    upper := endpoint122 }

noncomputable def innerPair410Input : RationalEnclosure :=
  { lower := (7019619/16777216), upper := (57509/131072) }

set_option maxRecDepth 1000000 in
private theorem innerPair410Input_eq :
    innerPair410Input = outerEnclosure 24 innerPair410Data.output := by
  rfl'

theorem innerPair410RoundedFacts :
    InnerPairRoundedFacts innerPair410Data innerPair410Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair410Input_eq }

noncomputable def innerPair411Data : WideLogData :=
  { lower := endpoint121
    upper := endpoint124 }

noncomputable def innerPair411Input : RationalEnclosure :=
  { lower := (7019619/16777216), upper := (7191255/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair411Input_eq :
    innerPair411Input = outerEnclosure 24 innerPair411Data.output := by
  rfl'

theorem innerPair411RoundedFacts :
    InnerPairRoundedFacts innerPair411Data innerPair411Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair411Input_eq }

noncomputable def innerPair412Data : WideLogData :=
  { lower := endpoint123
    upper := endpoint112 }

noncomputable def innerPair412Input : RationalEnclosure :=
  { lower := (6846209/16777216), upper := (7105657/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair412Input_eq :
    innerPair412Input = outerEnclosure 24 innerPair412Data.output := by
  rfl'

theorem innerPair412RoundedFacts :
    InnerPairRoundedFacts innerPair412Data innerPair412Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair412Input_eq }

noncomputable def innerPair413Data : WideLogData :=
  { lower := endpoint123
    upper := endpoint121 }

noncomputable def innerPair413Input : RationalEnclosure :=
  { lower := (6846209/16777216), upper := (1754905/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair413Input_eq :
    innerPair413Input = outerEnclosure 24 innerPair413Data.output := by
  rfl'

theorem innerPair413RoundedFacts :
    InnerPairRoundedFacts innerPair413Data innerPair413Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair413Input_eq }

noncomputable def innerPair414Data : WideLogData :=
  { lower := endpoint123
    upper := endpoint124 }

noncomputable def innerPair414Input : RationalEnclosure :=
  { lower := (6846209/16777216), upper := (7191255/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair414Input_eq :
    innerPair414Input = outerEnclosure 24 innerPair414Data.output := by
  rfl'

theorem innerPair414RoundedFacts :
    InnerPairRoundedFacts innerPair414Data innerPair414Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair414Input_eq }

noncomputable def innerPair415Data : WideLogData :=
  { lower := endpoint124
    upper := endpoint165 }

noncomputable def innerPair415Input : RationalEnclosure :=
  { lower := (3595627/8388608), upper := (1861365/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair415Input_eq :
    innerPair415Input = outerEnclosure 24 innerPair415Data.output := by
  rfl'

theorem innerPair415RoundedFacts :
    InnerPairRoundedFacts innerPair415Data innerPair415Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair415Input_eq }

noncomputable def innerPair416Data : WideLogData :=
  { lower := endpoint126
    upper := endpoint59 }

noncomputable def innerPair416Input : RationalEnclosure :=
  { lower := (4092875/8388608), upper := (8700795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair416Input_eq :
    innerPair416Input = outerEnclosure 24 innerPair416Data.output := by
  rfl'

theorem innerPair416RoundedFacts :
    InnerPairRoundedFacts innerPair416Data innerPair416Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair416Input_eq }

noncomputable def innerPair417Data : WideLogData :=
  { lower := endpoint128
    upper := endpoint129 }

noncomputable def innerPair417Input : RationalEnclosure :=
  { lower := (3769901/8388608), upper := (7850501/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair417Input_eq :
    innerPair417Input = outerEnclosure 24 innerPair417Data.output := by
  rfl'

theorem innerPair417RoundedFacts :
    InnerPairRoundedFacts innerPair417Data innerPair417Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair417Input_eq }

noncomputable def innerPair418Data : WideLogData :=
  { lower := endpoint130
    upper := endpoint131 }

noncomputable def innerPair418Input : RationalEnclosure :=
  { lower := (3847935/8388608), upper := (4012021/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair418Input_eq :
    innerPair418Input = outerEnclosure 24 innerPair418Data.output := by
  rfl'

theorem innerPair418RoundedFacts :
    InnerPairRoundedFacts innerPair418Data innerPair418Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair418Input_eq }

noncomputable def innerPair419Data : WideLogData :=
  { lower := endpoint131
    upper := endpoint167 }

noncomputable def innerPair419Input : RationalEnclosure :=
  { lower := (8024041/16777216), upper := (514121/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair419Input_eq :
    innerPair419Input = outerEnclosure 24 innerPair419Data.output := by
  rfl'

theorem innerPair419RoundedFacts :
    InnerPairRoundedFacts innerPair419Data innerPair419Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair419Input_eq }

noncomputable def innerPair420Data : WideLogData :=
  { lower := endpoint133
    upper := endpoint20 }

noncomputable def innerPair420Input : RationalEnclosure :=
  { lower := (4311289/8388608), upper := (8933277/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair420Input_eq :
    innerPair420Input = outerEnclosure 24 innerPair420Data.output := by
  rfl'

theorem innerPair420RoundedFacts :
    InnerPairRoundedFacts innerPair420Data innerPair420Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair420Input_eq }

noncomputable def innerPair421Data : WideLogData :=
  { lower := endpoint133
    upper := endpoint62 }

noncomputable def innerPair421Input : RationalEnclosure :=
  { lower := (4311289/8388608), upper := (9086495/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair421Input_eq :
    innerPair421Input = outerEnclosure 24 innerPair421Data.output := by
  rfl'

theorem innerPair421RoundedFacts :
    InnerPairRoundedFacts innerPair421Data innerPair421Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair421Input_eq }

noncomputable def innerPair422Data : WideLogData :=
  { lower := endpoint133
    upper := endpoint136 }

noncomputable def innerPair422Input : RationalEnclosure :=
  { lower := (4311289/8388608), upper := (8971713/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair422Input_eq :
    innerPair422Input = outerEnclosure 24 innerPair422Data.output := by
  rfl'

theorem innerPair422RoundedFacts :
    InnerPairRoundedFacts innerPair422Data innerPair422Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair422Input_eq }

noncomputable def innerPair423Data : WideLogData :=
  { lower := endpoint133
    upper := endpoint137 }

noncomputable def innerPair423Input : RationalEnclosure :=
  { lower := (4311289/8388608), upper := (8856141/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair423Input_eq :
    innerPair423Input = outerEnclosure 24 innerPair423Data.output := by
  rfl'

theorem innerPair423RoundedFacts :
    InnerPairRoundedFacts innerPair423Data innerPair423Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair423Input_eq }

noncomputable def innerPair424Data : WideLogData :=
  { lower := endpoint134
    upper := endpoint59 }

noncomputable def innerPair424Input : RationalEnclosure :=
  { lower := (8504567/16777216), upper := (8700795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair424Input_eq :
    innerPair424Input = outerEnclosure 24 innerPair424Data.output := by
  rfl'

theorem innerPair424RoundedFacts :
    InnerPairRoundedFacts innerPair424Data innerPair424Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair424Input_eq }

noncomputable def innerPair425Data : WideLogData :=
  { lower := endpoint135
    upper := endpoint58 }

noncomputable def innerPair425Input : RationalEnclosure :=
  { lower := (1048215/2097152), upper := (4369883/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair425Input_eq :
    innerPair425Input = outerEnclosure 24 innerPair425Data.output := by
  rfl'

theorem innerPair425RoundedFacts :
    InnerPairRoundedFacts innerPair425Data innerPair425Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair425Input_eq }

noncomputable def innerPair426Data : WideLogData :=
  { lower := endpoint135
    upper := endpoint59 }

noncomputable def innerPair426Input : RationalEnclosure :=
  { lower := (1048215/2097152), upper := (8700795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair426Input_eq :
    innerPair426Input = outerEnclosure 24 innerPair426Data.output := by
  rfl'

theorem innerPair426RoundedFacts :
    InnerPairRoundedFacts innerPair426Data innerPair426Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair426Input_eq }

noncomputable def innerPair427Data : WideLogData :=
  { lower := endpoint135
    upper := endpoint200 }

noncomputable def innerPair427Input : RationalEnclosure :=
  { lower := (1048215/2097152), upper := (4291667/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair427Input_eq :
    innerPair427Input = outerEnclosure 24 innerPair427Data.output := by
  rfl'

theorem innerPair427RoundedFacts :
    InnerPairRoundedFacts innerPair427Data innerPair427Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair427Input_eq }

noncomputable def innerPair428Data : WideLogData :=
  { lower := endpoint137
    upper := endpoint138 }

noncomputable def innerPair428Input : RationalEnclosure :=
  { lower := (2214035/4194304), upper := (4581291/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair428Input_eq :
    innerPair428Input = outerEnclosure 24 innerPair428Data.output := by
  rfl'

theorem innerPair428RoundedFacts :
    InnerPairRoundedFacts innerPair428Data innerPair428Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair428Input_eq }

noncomputable def innerPair429Data : WideLogData :=
  { lower := endpoint138
    upper := endpoint66 }

noncomputable def innerPair429Input : RationalEnclosure :=
  { lower := (9162581/16777216), upper := (9463527/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair429Input_eq :
    innerPair429Input = outerEnclosure 24 innerPair429Data.output := by
  rfl'

theorem innerPair429RoundedFacts :
    InnerPairRoundedFacts innerPair429Data innerPair429Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair429Input_eq }

noncomputable def innerPair430Data : WideLogData :=
  { lower := endpoint139
    upper := endpoint63 }

noncomputable def innerPair430Input : RationalEnclosure :=
  { lower := (9238325/16777216), upper := (9537927/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair430Input_eq :
    innerPair430Input = outerEnclosure 24 innerPair430Data.output := by
  rfl'

theorem innerPair430RoundedFacts :
    InnerPairRoundedFacts innerPair430Data innerPair430Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair430Input_eq }

noncomputable def innerPair431Data : WideLogData :=
  { lower := endpoint139
    upper := endpoint68 }

noncomputable def innerPair431Input : RationalEnclosure :=
  { lower := (9238325/16777216), upper := (9685745/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair431Input_eq :
    innerPair431Input = outerEnclosure 24 innerPair431Data.output := by
  rfl'

theorem innerPair431RoundedFacts :
    InnerPairRoundedFacts innerPair431Data innerPair431Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair431Input_eq }

noncomputable def innerPair432Data : WideLogData :=
  { lower := endpoint139
    upper := endpoint178 }

noncomputable def innerPair432Input : RationalEnclosure :=
  { lower := (9238325/16777216), upper := (9426203/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair432Input_eq :
    innerPair432Input = outerEnclosure 24 innerPair432Data.output := by
  rfl'

theorem innerPair432RoundedFacts :
    InnerPairRoundedFacts innerPair432Data innerPair432Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair432Input_eq }

noncomputable def innerPair433Data : WideLogData :=
  { lower := endpoint139
    upper := endpoint181 }

noncomputable def innerPair433Input : RationalEnclosure :=
  { lower := (9238325/16777216), upper := (9528645/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair433Input_eq :
    innerPair433Input = outerEnclosure 24 innerPair433Data.output := by
  rfl'

theorem innerPair433RoundedFacts :
    InnerPairRoundedFacts innerPair433Data innerPair433Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair433Input_eq }

noncomputable def innerPair434Data : WideLogData :=
  { lower := endpoint140
    upper := endpoint141 }

noncomputable def innerPair434Input : RationalEnclosure :=
  { lower := (192139/4194304), upper := (1503443/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair434Input_eq :
    innerPair434Input = outerEnclosure 24 innerPair434Data.output := by
  rfl'

theorem innerPair434RoundedFacts :
    InnerPairRoundedFacts innerPair434Data innerPair434Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair434Input_eq }

noncomputable def innerPair435Data : WideLogData :=
  { lower := endpoint142
    upper := endpoint33 }

noncomputable def innerPair435Input : RationalEnclosure :=
  { lower := (3265105/16777216), upper := (3691217/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair435Input_eq :
    innerPair435Input = outerEnclosure 24 innerPair435Data.output := by
  rfl'

theorem innerPair435RoundedFacts :
    InnerPairRoundedFacts innerPair435Data innerPair435Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair435Input_eq }

noncomputable def innerPair436Data : WideLogData :=
  { lower := endpoint143
    upper := endpoint144 }

noncomputable def innerPair436Input : RationalEnclosure :=
  { lower := (4209073/16777216), upper := (278883/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair436Input_eq :
    innerPair436Input = outerEnclosure 24 innerPair436Data.output := by
  rfl'

theorem innerPair436RoundedFacts :
    InnerPairRoundedFacts innerPair436Data innerPair436Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair436Input_eq }

noncomputable def innerPair437Data : WideLogData :=
  { lower := endpoint145
    upper := endpoint146 }

noncomputable def innerPair437Input : RationalEnclosure :=
  { lower := (4386611/16777216), upper := (4624591/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair437Input_eq :
    innerPair437Input = outerEnclosure 24 innerPair437Data.output := by
  rfl'

theorem innerPair437RoundedFacts :
    InnerPairRoundedFacts innerPair437Data innerPair437Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair437Input_eq }

noncomputable def innerPair438Data : WideLogData :=
  { lower := endpoint148
    upper := endpoint149 }

noncomputable def innerPair438Input : RationalEnclosure :=
  { lower := (1026693/4194304), upper := (2205911/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair438Input_eq :
    innerPair438Input = outerEnclosure 24 innerPair438Data.output := by
  rfl'

theorem innerPair438RoundedFacts :
    InnerPairRoundedFacts innerPair438Data innerPair438Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair438Input_eq }

noncomputable def innerPair439Data : WideLogData :=
  { lower := endpoint150
    upper := endpoint143 }

noncomputable def innerPair439Input : RationalEnclosure :=
  { lower := (3900281/16777216), upper := (2104537/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair439Input_eq :
    innerPair439Input = outerEnclosure 24 innerPair439Data.output := by
  rfl'

theorem innerPair439RoundedFacts :
    InnerPairRoundedFacts innerPair439Data innerPair439Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair439Input_eq }

noncomputable def innerPair440Data : WideLogData :=
  { lower := endpoint151
    upper := endpoint25 }

noncomputable def innerPair440Input : RationalEnclosure :=
  { lower := (1262039/16777216), upper := (870711/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair440Input_eq :
    innerPair440Input = outerEnclosure 24 innerPair440Data.output := by
  rfl'

theorem innerPair440RoundedFacts :
    InnerPairRoundedFacts innerPair440Data innerPair440Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair440Input_eq }

noncomputable def innerPair441Data : WideLogData :=
  { lower := endpoint152
    upper := endpoint153 }

noncomputable def innerPair441Input : RationalEnclosure :=
  { lower := (3861279/16777216), upper := (4119595/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair441Input_eq :
    innerPair441Input = outerEnclosure 24 innerPair441Data.output := by
  rfl'

theorem innerPair441RoundedFacts :
    InnerPairRoundedFacts innerPair441Data innerPair441Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair441Input_eq }

noncomputable def innerPair442Data : WideLogData :=
  { lower := endpoint155
    upper := endpoint108 }

noncomputable def innerPair442Input : RationalEnclosure :=
  { lower := (6042891/16777216), upper := (6314961/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair442Input_eq :
    innerPair442Input = outerEnclosure 24 innerPair442Data.output := by
  rfl'

theorem innerPair442RoundedFacts :
    InnerPairRoundedFacts innerPair442Data innerPair442Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair442Input_eq }

noncomputable def innerPair443Data : WideLogData :=
  { lower := endpoint156
    upper := endpoint160 }

noncomputable def innerPair443Input : RationalEnclosure :=
  { lower := (2998557/8388608), upper := (794985/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair443Input_eq :
    innerPair443Input = outerEnclosure 24 innerPair443Data.output := by
  rfl'

theorem innerPair443RoundedFacts :
    InnerPairRoundedFacts innerPair443Data innerPair443Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair443Input_eq }

noncomputable def innerPair444Data : WideLogData :=
  { lower := endpoint157
    upper := endpoint109 }

noncomputable def innerPair444Input : RationalEnclosure :=
  { lower := (5859029/16777216), upper := (6134073/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair444Input_eq :
    innerPair444Input = outerEnclosure 24 innerPair444Data.output := by
  rfl'

theorem innerPair444RoundedFacts :
    InnerPairRoundedFacts innerPair444Data innerPair444Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair444Input_eq }

noncomputable def innerPair445Data : WideLogData :=
  { lower := endpoint158
    upper := endpoint159 }

noncomputable def innerPair445Input : RationalEnclosure :=
  { lower := (3010009/8388608), upper := (3119443/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair445Input_eq :
    innerPair445Input = outerEnclosure 24 innerPair445Data.output := by
  rfl'

theorem innerPair445RoundedFacts :
    InnerPairRoundedFacts innerPair445Data innerPair445Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair445Input_eq }

noncomputable def innerPair446Data : WideLogData :=
  { lower := endpoint161
    upper := endpoint111 }

noncomputable def innerPair446Input : RationalEnclosure :=
  { lower := (778095/2097152), upper := (205709/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair446Input_eq :
    innerPair446Input = outerEnclosure 24 innerPair446Data.output := by
  rfl'

theorem innerPair446RoundedFacts :
    InnerPairRoundedFacts innerPair446Data innerPair446Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair446Input_eq }

noncomputable def innerPair447Data : WideLogData :=
  { lower := endpoint161
    upper := endpoint194 }

noncomputable def innerPair447Input : RationalEnclosure :=
  { lower := (778095/2097152), upper := (202935/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair447Input_eq :
    innerPair447Input = outerEnclosure 24 innerPair447Data.output := by
  rfl'

theorem innerPair447RoundedFacts :
    InnerPairRoundedFacts innerPair447Data innerPair447Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair447Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
