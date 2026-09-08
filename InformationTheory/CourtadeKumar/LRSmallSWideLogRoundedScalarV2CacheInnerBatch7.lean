import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch0
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch2
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch3

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

noncomputable def innerPair448Data : WideLogData :=
  { lower := endpoint162
    upper := endpoint163 }

noncomputable def innerPair448Input : RationalEnclosure :=
  { lower := (5812747/16777216), upper := (3089739/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair448Input_eq :
    innerPair448Input = outerEnclosure 24 innerPair448Data.output := by
  rfl'

theorem innerPair448RoundedFacts :
    InnerPairRoundedFacts innerPair448Data innerPair448Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair448Input_eq }

noncomputable def innerPair449Data : WideLogData :=
  { lower := endpoint164
    upper := endpoint124 }

noncomputable def innerPair449Input : RationalEnclosure :=
  { lower := (3466569/8388608), upper := (7191255/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair449Input_eq :
    innerPair449Input = outerEnclosure 24 innerPair449Data.output := by
  rfl'

theorem innerPair449RoundedFacts :
    InnerPairRoundedFacts innerPair449Data innerPair449Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair449Input_eq }

noncomputable def innerPair450Data : WideLogData :=
  { lower := endpoint165
    upper := endpoint130 }

noncomputable def innerPair450Input : RationalEnclosure :=
  { lower := (7445459/16777216), upper := (7695871/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair450Input_eq :
    innerPair450Input = outerEnclosure 24 innerPair450Data.output := by
  rfl'

theorem innerPair450RoundedFacts :
    InnerPairRoundedFacts innerPair450Data innerPair450Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair450Input_eq }

noncomputable def innerPair451Data : WideLogData :=
  { lower := endpoint169
    upper := endpoint170 }

noncomputable def innerPair451Input : RationalEnclosure :=
  { lower := (1916193/4194304), upper := (985157/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair451Input_eq :
    innerPair451Input = outerEnclosure 24 innerPair451Data.output := by
  rfl'

theorem innerPair451RoundedFacts :
    InnerPairRoundedFacts innerPair451Data innerPair451Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair451Input_eq }

noncomputable def innerPair452Data : WideLogData :=
  { lower := endpoint171
    upper := endpoint59 }

noncomputable def innerPair452Input : RationalEnclosure :=
  { lower := (2086479/4194304), upper := (8700795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair452Input_eq :
    innerPair452Input = outerEnclosure 24 innerPair452Data.output := by
  rfl'

theorem innerPair452RoundedFacts :
    InnerPairRoundedFacts innerPair452Data innerPair452Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair452Input_eq }

noncomputable def innerPair453Data : WideLogData :=
  { lower := endpoint171
    upper := endpoint199 }

noncomputable def innerPair453Input : RationalEnclosure :=
  { lower := (2086479/4194304), upper := (8543997/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair453Input_eq :
    innerPair453Input = outerEnclosure 24 innerPair453Data.output := by
  rfl'

theorem innerPair453RoundedFacts :
    InnerPairRoundedFacts innerPair453Data innerPair453Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair453Input_eq }

noncomputable def innerPair454Data : WideLogData :=
  { lower := endpoint172
    upper := endpoint173 }

noncomputable def innerPair454Input : RationalEnclosure :=
  { lower := (255097/524288), upper := (4180427/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair454Input_eq :
    innerPair454Input = outerEnclosure 24 innerPair454Data.output := by
  rfl'

theorem innerPair454RoundedFacts :
    InnerPairRoundedFacts innerPair454Data innerPair454Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair454Input_eq }

noncomputable def innerPair455Data : WideLogData :=
  { lower := endpoint174
    upper := endpoint56 }

noncomputable def innerPair455Input : RationalEnclosure :=
  { lower := (8425429/16777216), upper := (8661733/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair455Input_eq :
    innerPair455Input = outerEnclosure 24 innerPair455Data.output := by
  rfl'

theorem innerPair455RoundedFacts :
    InnerPairRoundedFacts innerPair455Data innerPair455Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair455Input_eq }

noncomputable def innerPair456Data : WideLogData :=
  { lower := endpoint174
    upper := endpoint58 }

noncomputable def innerPair456Input : RationalEnclosure :=
  { lower := (8425429/16777216), upper := (4369883/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair456Input_eq :
    innerPair456Input = outerEnclosure 24 innerPair456Data.output := by
  rfl'

theorem innerPair456RoundedFacts :
    InnerPairRoundedFacts innerPair456Data innerPair456Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair456Input_eq }

noncomputable def innerPair457Data : WideLogData :=
  { lower := endpoint176
    upper := endpoint177 }

noncomputable def innerPair457Input : RationalEnclosure :=
  { lower := (8952505/16777216), upper := (4623885/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair457Input_eq :
    innerPair457Input = outerEnclosure 24 innerPair457Data.output := by
  rfl'

theorem innerPair457RoundedFacts :
    InnerPairRoundedFacts innerPair457Data innerPair457Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair457Input_eq }

noncomputable def innerPair458Data : WideLogData :=
  { lower := endpoint178
    upper := endpoint219 }

noncomputable def innerPair458Input : RationalEnclosure :=
  { lower := (4713101/8388608), upper := (9648913/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair458Input_eq :
    innerPair458Input = outerEnclosure 24 innerPair458Data.output := by
  rfl'

theorem innerPair458RoundedFacts :
    InnerPairRoundedFacts innerPair458Data innerPair458Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair458Input_eq }

noncomputable def innerPair459Data : WideLogData :=
  { lower := endpoint179
    upper := endpoint66 }

noncomputable def innerPair459Input : RationalEnclosure :=
  { lower := (9124581/16777216), upper := (9463527/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair459Input_eq :
    innerPair459Input = outerEnclosure 24 innerPair459Data.output := by
  rfl'

theorem innerPair459RoundedFacts :
    InnerPairRoundedFacts innerPair459Data innerPair459Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair459Input_eq }

noncomputable def innerPair460Data : WideLogData :=
  { lower := endpoint179
    upper := endpoint214 }

noncomputable def innerPair460Input : RationalEnclosure :=
  { lower := (9124581/16777216), upper := (9313729/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair460Input_eq :
    innerPair460Input = outerEnclosure 24 innerPair460Data.output := by
  rfl'

theorem innerPair460RoundedFacts :
    InnerPairRoundedFacts innerPair460Data innerPair460Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair460Input_eq }

noncomputable def innerPair461Data : WideLogData :=
  { lower := endpoint179
    upper := endpoint217 }

noncomputable def innerPair461Input : RationalEnclosure :=
  { lower := (9124581/16777216), upper := (9611999/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair461Input_eq :
    innerPair461Input = outerEnclosure 24 innerPair461Data.output := by
  rfl'

theorem innerPair461RoundedFacts :
    InnerPairRoundedFacts innerPair461Data innerPair461Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair461Input_eq }

noncomputable def innerPair462Data : WideLogData :=
  { lower := endpoint180
    upper := endpoint60 }

noncomputable def innerPair462Input : RationalEnclosure :=
  { lower := (575031/1048576), upper := (296899/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair462Input_eq :
    innerPair462Input = outerEnclosure 24 innerPair462Data.output := by
  rfl'

theorem innerPair462RoundedFacts :
    InnerPairRoundedFacts innerPair462Data innerPair462Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair462Input_eq }

noncomputable def innerPair463Data : WideLogData :=
  { lower := endpoint180
    upper := endpoint178 }

noncomputable def innerPair463Input : RationalEnclosure :=
  { lower := (575031/1048576), upper := (9426203/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair463Input_eq :
    innerPair463Input = outerEnclosure 24 innerPair463Data.output := by
  rfl'

theorem innerPair463RoundedFacts :
    InnerPairRoundedFacts innerPair463Data innerPair463Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair463Input_eq }

noncomputable def innerPair464Data : WideLogData :=
  { lower := endpoint183
    upper := endpoint221 }

noncomputable def innerPair464Input : RationalEnclosure :=
  { lower := (75957/131072), upper := (9941333/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair464Input_eq :
    innerPair464Input = outerEnclosure 24 innerPair464Data.output := by
  rfl'

theorem innerPair464RoundedFacts :
    InnerPairRoundedFacts innerPair464Data innerPair464Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair464Input_eq }

noncomputable def innerPair465Data : WideLogData :=
  { lower := endpoint184
    upper := endpoint186 }

noncomputable def innerPair465Input : RationalEnclosure :=
  { lower := (9795759/16777216), upper := (10013649/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair465Input_eq :
    innerPair465Input = outerEnclosure 24 innerPair465Data.output := by
  rfl'

theorem innerPair465RoundedFacts :
    InnerPairRoundedFacts innerPair465Data innerPair465Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair465Input_eq }

noncomputable def innerPair466Data : WideLogData :=
  { lower := endpoint185
    upper := endpoint188 }

noncomputable def innerPair466Input : RationalEnclosure :=
  { lower := (9905057/16777216), upper := (5042827/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair466Input_eq :
    innerPair466Input = outerEnclosure 24 innerPair466Data.output := by
  rfl'

theorem innerPair466RoundedFacts :
    InnerPairRoundedFacts innerPair466Data innerPair466Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair466Input_eq }

noncomputable def innerPair467Data : WideLogData :=
  { lower := endpoint186
    upper := endpoint189 }

noncomputable def innerPair467Input : RationalEnclosure :=
  { lower := (625853/1048576), upper := (5096543/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair467Input_eq :
    innerPair467Input = outerEnclosure 24 innerPair467Data.output := by
  rfl'

theorem innerPair467RoundedFacts :
    InnerPairRoundedFacts innerPair467Data innerPair467Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair467Input_eq }

noncomputable def innerPair468Data : WideLogData :=
  { lower := endpoint187
    upper := endpoint188 }

noncomputable def innerPair468Input : RationalEnclosure :=
  { lower := (308397/524288), upper := (5042827/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair468Input_eq :
    innerPair468Input = outerEnclosure 24 innerPair468Data.output := by
  rfl'

theorem innerPair468RoundedFacts :
    InnerPairRoundedFacts innerPair468Data innerPair468Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair468Input_eq }

noncomputable def innerPair469Data : WideLogData :=
  { lower := endpoint187
    upper := endpoint189 }

noncomputable def innerPair469Input : RationalEnclosure :=
  { lower := (308397/524288), upper := (5096543/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair469Input_eq :
    innerPair469Input = outerEnclosure 24 innerPair469Data.output := by
  rfl'

theorem innerPair469RoundedFacts :
    InnerPairRoundedFacts innerPair469Data innerPair469Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair469Input_eq }

noncomputable def innerPair470Data : WideLogData :=
  { lower := endpoint188
    upper := endpoint223 }

noncomputable def innerPair470Input : RationalEnclosure :=
  { lower := (10085653/16777216), upper := (5149917/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair470Input_eq :
    innerPair470Input = outerEnclosure 24 innerPair470Data.output := by
  rfl'

theorem innerPair470RoundedFacts :
    InnerPairRoundedFacts innerPair470Data innerPair470Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair470Input_eq }

noncomputable def innerPair471Data : WideLogData :=
  { lower := endpoint188
    upper := endpoint237 }

noncomputable def innerPair471Input : RationalEnclosure :=
  { lower := (10085653/16777216), upper := (10335267/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair471Input_eq :
    innerPair471Input = outerEnclosure 24 innerPair471Data.output := by
  rfl'

theorem innerPair471RoundedFacts :
    InnerPairRoundedFacts innerPair471Data innerPair471Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair471Input_eq }

noncomputable def innerPair472Data : WideLogData :=
  { lower := endpoint190
    upper := endpoint191 }

noncomputable def innerPair472Input : RationalEnclosure :=
  { lower := (3269181/8388608), upper := (6758829/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair472Input_eq :
    innerPair472Input = outerEnclosure 24 innerPair472Data.output := by
  rfl'

theorem innerPair472RoundedFacts :
    InnerPairRoundedFacts innerPair472Data innerPair472Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair472Input_eq }

noncomputable def innerPair473Data : WideLogData :=
  { lower := endpoint192
    upper := endpoint193 }

noncomputable def innerPair473Input : RationalEnclosure :=
  { lower := (1754647/4194304), upper := (3610955/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair473Input_eq :
    innerPair473Input = outerEnclosure 24 innerPair473Data.output := by
  rfl'

theorem innerPair473RoundedFacts :
    InnerPairRoundedFacts innerPair473Data innerPair473Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair473Input_eq }

noncomputable def innerPair474Data : WideLogData :=
  { lower := endpoint195
    upper := endpoint196 }

noncomputable def innerPair474Input : RationalEnclosure :=
  { lower := (3202339/8388608), upper := (3335495/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair474Input_eq :
    innerPair474Input = outerEnclosure 24 innerPair474Data.output := by
  rfl'

theorem innerPair474RoundedFacts :
    InnerPairRoundedFacts innerPair474Data innerPair474Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair474Input_eq }

noncomputable def innerPair475Data : WideLogData :=
  { lower := endpoint197
    upper := endpoint198 }

noncomputable def innerPair475Input : RationalEnclosure :=
  { lower := (1765673/4194304), upper := (7233891/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair475Input_eq :
    innerPair475Input = outerEnclosure 24 innerPair475Data.output := by
  rfl'

theorem innerPair475RoundedFacts :
    InnerPairRoundedFacts innerPair475Data innerPair475Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair475Input_eq }

noncomputable def innerPair476Data : WideLogData :=
  { lower := endpoint200
    upper := endpoint205 }

noncomputable def innerPair476Input : RationalEnclosure :=
  { lower := (8583333/16777216), upper := (8817439/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair476Input_eq :
    innerPair476Input = outerEnclosure 24 innerPair476Data.output := by
  rfl'

theorem innerPair476RoundedFacts :
    InnerPairRoundedFacts innerPair476Data innerPair476Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair476Input_eq }

noncomputable def innerPair477Data : WideLogData :=
  { lower := endpoint201
    upper := endpoint202 }

noncomputable def innerPair477Input : RationalEnclosure :=
  { lower := (2133537/4194304), upper := (545627/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair477Input_eq :
    innerPair477Input = outerEnclosure 24 innerPair477Data.output := by
  rfl'

theorem innerPair477RoundedFacts :
    InnerPairRoundedFacts innerPair477Data innerPair477Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair477Input_eq }

noncomputable def innerPair478Data : WideLogData :=
  { lower := endpoint203
    upper := endpoint204 }

noncomputable def innerPair478Input : RationalEnclosure :=
  { lower := (8410549/16777216), upper := (4299031/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair478Input_eq :
    innerPair478Input = outerEnclosure 24 innerPair478Data.output := by
  rfl'

theorem innerPair478RoundedFacts :
    InnerPairRoundedFacts innerPair478Data innerPair478Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair478Input_eq }

noncomputable def innerPair479Data : WideLogData :=
  { lower := endpoint206
    upper := endpoint207 }

noncomputable def innerPair479Input : RationalEnclosure :=
  { lower := (8788353/16777216), upper := (2245327/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair479Input_eq :
    innerPair479Input = outerEnclosure 24 innerPair479Data.output := by
  rfl'

theorem innerPair479RoundedFacts :
    InnerPairRoundedFacts innerPair479Data innerPair479Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair479Input_eq }

noncomputable def innerPair480Data : WideLogData :=
  { lower := endpoint208
    upper := endpoint209 }

noncomputable def innerPair480Input : RationalEnclosure :=
  { lower := (4471447/8388608), upper := (4567045/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair480Input_eq :
    innerPair480Input = outerEnclosure 24 innerPair480Data.output := by
  rfl'

theorem innerPair480RoundedFacts :
    InnerPairRoundedFacts innerPair480Data innerPair480Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair480Input_eq }

noncomputable def innerPair481Data : WideLogData :=
  { lower := endpoint210
    upper := endpoint177 }

noncomputable def innerPair481Input : RationalEnclosure :=
  { lower := (4533709/8388608), upper := (4623885/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair481Input_eq :
    innerPair481Input = outerEnclosure 24 innerPair481Data.output := by
  rfl'

theorem innerPair481RoundedFacts :
    InnerPairRoundedFacts innerPair481Data innerPair481Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair481Input_eq }

noncomputable def innerPair482Data : WideLogData :=
  { lower := endpoint211
    upper := endpoint69 }

noncomputable def innerPair482Input : RationalEnclosure :=
  { lower := (10405907/16777216), upper := (10685535/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair482Input_eq :
    innerPair482Input = outerEnclosure 24 innerPair482Data.output := by
  rfl'

theorem innerPair482RoundedFacts :
    InnerPairRoundedFacts innerPair482Data innerPair482Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair482Input_eq }

noncomputable def innerPair483Data : WideLogData :=
  { lower := endpoint211
    upper := endpoint70 }

noncomputable def innerPair483Input : RationalEnclosure :=
  { lower := (10405907/16777216), upper := (2705905/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair483Input_eq :
    innerPair483Input = outerEnclosure 24 innerPair483Data.output := by
  rfl'

theorem innerPair483RoundedFacts :
    InnerPairRoundedFacts innerPair483Data innerPair483Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair483Input_eq }

noncomputable def innerPair484Data : WideLogData :=
  { lower := endpoint211
    upper := endpoint81 }

noncomputable def innerPair484Input : RationalEnclosure :=
  { lower := (10405907/16777216), upper := (10960577/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair484Input_eq :
    innerPair484Input = outerEnclosure 24 innerPair484Data.output := by
  rfl'

theorem innerPair484RoundedFacts :
    InnerPairRoundedFacts innerPair484Data innerPair484Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair484Input_eq }

noncomputable def innerPair485Data : WideLogData :=
  { lower := endpoint211
    upper := endpoint245 }

noncomputable def innerPair485Input : RationalEnclosure :=
  { lower := (10405907/16777216), upper := (10650835/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair485Input_eq :
    innerPair485Input = outerEnclosure 24 innerPair485Data.output := by
  rfl'

theorem innerPair485RoundedFacts :
    InnerPairRoundedFacts innerPair485Data innerPair485Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair485Input_eq }

noncomputable def innerPair486Data : WideLogData :=
  { lower := endpoint211
    upper := endpoint252 }

noncomputable def innerPair486Input : RationalEnclosure :=
  { lower := (10405907/16777216), upper := (41469/65536) }

set_option maxRecDepth 1000000 in
private theorem innerPair486Input_eq :
    innerPair486Input = outerEnclosure 24 innerPair486Data.output := by
  rfl'

theorem innerPair486RoundedFacts :
    InnerPairRoundedFacts innerPair486Data innerPair486Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair486Input_eq }

noncomputable def innerPair487Data : WideLogData :=
  { lower := endpoint212
    upper := endpoint213 }

noncomputable def innerPair487Input : RationalEnclosure :=
  { lower := (9048321/16777216), upper := (4638035/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair487Input_eq :
    innerPair487Input = outerEnclosure 24 innerPair487Data.output := by
  rfl'

theorem innerPair487RoundedFacts :
    InnerPairRoundedFacts innerPair487Data innerPair487Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair487Input_eq }

noncomputable def innerPair488Data : WideLogData :=
  { lower := endpoint213
    upper := endpoint60 }

noncomputable def innerPair488Input : RationalEnclosure :=
  { lower := (9276069/16777216), upper := (296899/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair488Input_eq :
    innerPair488Input = outerEnclosure 24 innerPair488Data.output := by
  rfl'

theorem innerPair488RoundedFacts :
    InnerPairRoundedFacts innerPair488Data innerPair488Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair488Input_eq }

noncomputable def innerPair489Data : WideLogData :=
  { lower := endpoint213
    upper := endpoint66 }

noncomputable def innerPair489Input : RationalEnclosure :=
  { lower := (9276069/16777216), upper := (9463527/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair489Input_eq :
    innerPair489Input = outerEnclosure 24 innerPair489Data.output := by
  rfl'

theorem innerPair489RoundedFacts :
    InnerPairRoundedFacts innerPair489Data innerPair489Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair489Input_eq }

noncomputable def innerPair490Data : WideLogData :=
  { lower := endpoint215
    upper := endpoint216 }

noncomputable def innerPair490Input : RationalEnclosure :=
  { lower := (9351303/16777216), upper := (2393751/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair490Input_eq :
    innerPair490Input = outerEnclosure 24 innerPair490Data.output := by
  rfl'

theorem innerPair490RoundedFacts :
    InnerPairRoundedFacts innerPair490Data innerPair490Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair490Input_eq }

noncomputable def innerPair491Data : WideLogData :=
  { lower := endpoint216
    upper := endpoint184 }

noncomputable def innerPair491Input : RationalEnclosure :=
  { lower := (9575003/16777216), upper := (612235/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair491Input_eq :
    innerPair491Input = outerEnclosure 24 innerPair491Data.output := by
  rfl'

theorem innerPair491RoundedFacts :
    InnerPairRoundedFacts innerPair491Data innerPair491Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair491Input_eq }

noncomputable def innerPair492Data : WideLogData :=
  { lower := endpoint216
    upper := endpoint185 }

noncomputable def innerPair492Input : RationalEnclosure :=
  { lower := (9575003/16777216), upper := (4952529/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair492Input_eq :
    innerPair492Input = outerEnclosure 24 innerPair492Data.output := by
  rfl'

theorem innerPair492RoundedFacts :
    InnerPairRoundedFacts innerPair492Data innerPair492Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair492Input_eq }

noncomputable def innerPair493Data : WideLogData :=
  { lower := endpoint216
    upper := endpoint220 }

noncomputable def innerPair493Input : RationalEnclosure :=
  { lower := (9575003/16777216), upper := (5024845/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair493Input_eq :
    innerPair493Input = outerEnclosure 24 innerPair493Data.output := by
  rfl'

theorem innerPair493RoundedFacts :
    InnerPairRoundedFacts innerPair493Data innerPair493Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair493Input_eq }

noncomputable def innerPair494Data : WideLogData :=
  { lower := endpoint219
    upper := endpoint187 }

noncomputable def innerPair494Input : RationalEnclosure :=
  { lower := (603057/1048576), upper := (9868705/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair494Input_eq :
    innerPair494Input = outerEnclosure 24 innerPair494Data.output := by
  rfl'

theorem innerPair494RoundedFacts :
    InnerPairRoundedFacts innerPair494Data innerPair494Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair494Input_eq }

noncomputable def innerPair495Data : WideLogData :=
  { lower := endpoint220
    upper := endpoint236 }

noncomputable def innerPair495Input : RationalEnclosure :=
  { lower := (10049689/16777216), upper := (1278593/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair495Input_eq :
    innerPair495Input = outerEnclosure 24 innerPair495Data.output := by
  rfl'

theorem innerPair495RoundedFacts :
    InnerPairRoundedFacts innerPair495Data innerPair495Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair495Input_eq }

noncomputable def innerPair496Data : WideLogData :=
  { lower := endpoint221
    upper := endpoint222 }

noncomputable def innerPair496Input : RationalEnclosure :=
  { lower := (2485333/4194304), upper := (1269669/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair496Input_eq :
    innerPair496Input = outerEnclosure 24 innerPair496Data.output := by
  rfl'

theorem innerPair496RoundedFacts :
    InnerPairRoundedFacts innerPair496Data innerPair496Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair496Input_eq }

noncomputable def innerPair497Data : WideLogData :=
  { lower := endpoint222
    upper := endpoint237 }

noncomputable def innerPair497Input : RationalEnclosure :=
  { lower := (10157351/16777216), upper := (10335267/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair497Input_eq :
    innerPair497Input = outerEnclosure 24 innerPair497Data.output := by
  rfl'

theorem innerPair497RoundedFacts :
    InnerPairRoundedFacts innerPair497Data innerPair497Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair497Input_eq }

noncomputable def innerPair498Data : WideLogData :=
  { lower := endpoint222
    upper := endpoint238 }

noncomputable def innerPair498Input : RationalEnclosure :=
  { lower := (10157351/16777216), upper := (10370625/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair498Input_eq :
    innerPair498Input = outerEnclosure 24 innerPair498Data.output := by
  rfl'

theorem innerPair498RoundedFacts :
    InnerPairRoundedFacts innerPair498Data innerPair498Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair498Input_eq }

noncomputable def innerPair499Data : WideLogData :=
  { lower := endpoint222
    upper := endpoint251 }

noncomputable def innerPair499Input : RationalEnclosure :=
  { lower := (10157351/16777216), upper := (10476253/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair499Input_eq :
    innerPair499Input = outerEnclosure 24 innerPair499Data.output := by
  rfl'

theorem innerPair499RoundedFacts :
    InnerPairRoundedFacts innerPair499Data innerPair499Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair499Input_eq }

noncomputable def innerPair500Data : WideLogData :=
  { lower := endpoint223
    upper := endpoint243 }

noncomputable def innerPair500Input : RationalEnclosure :=
  { lower := (10299833/16777216), upper := (10511315/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair500Input_eq :
    innerPair500Input = outerEnclosure 24 innerPair500Data.output := by
  rfl'

theorem innerPair500RoundedFacts :
    InnerPairRoundedFacts innerPair500Data innerPair500Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair500Input_eq }

noncomputable def innerPair501Data : WideLogData :=
  { lower := endpoint224
    upper := endpoint225 }

noncomputable def innerPair501Input : RationalEnclosure :=
  { lower := (9209961/16777216), upper := (9398155/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair501Input_eq :
    innerPair501Input = outerEnclosure 24 innerPair501Data.output := by
  rfl'

theorem innerPair501RoundedFacts :
    InnerPairRoundedFacts innerPair501Data innerPair501Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair501Input_eq }

noncomputable def innerPair502Data : WideLogData :=
  { lower := endpoint226
    upper := endpoint227 }

noncomputable def innerPair502Input : RationalEnclosure :=
  { lower := (2340171/4194304), upper := (2386801/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair502Input_eq :
    innerPair502Input = outerEnclosure 24 innerPair502Data.output := by
  rfl'

theorem innerPair502RoundedFacts :
    InnerPairRoundedFacts innerPair502Data innerPair502Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair502Input_eq }

noncomputable def innerPair503Data : WideLogData :=
  { lower := endpoint228
    upper := endpoint229 }

noncomputable def innerPair503Input : RationalEnclosure :=
  { lower := (9482157/16777216), upper := (603633/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair503Input_eq :
    innerPair503Input = outerEnclosure 24 innerPair503Data.output := by
  rfl'

theorem innerPair503RoundedFacts :
    InnerPairRoundedFacts innerPair503Data innerPair503Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair503Input_eq }

noncomputable def innerPair504Data : WideLogData :=
  { lower := endpoint230
    upper := endpoint231 }

noncomputable def innerPair504Input : RationalEnclosure :=
  { lower := (4810617/8388608), upper := (9804895/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair504Input_eq :
    innerPair504Input = outerEnclosure 24 innerPair504Data.output := by
  rfl'

theorem innerPair504RoundedFacts :
    InnerPairRoundedFacts innerPair504Data innerPair504Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair504Input_eq }

noncomputable def innerPair505Data : WideLogData :=
  { lower := endpoint232
    upper := endpoint233 }

noncomputable def innerPair505Input : RationalEnclosure :=
  { lower := (9510065/16777216), upper := (2422011/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair505Input_eq :
    innerPair505Input = outerEnclosure 24 innerPair505Data.output := by
  rfl'

theorem innerPair505RoundedFacts :
    InnerPairRoundedFacts innerPair505Data innerPair505Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair505Input_eq }

noncomputable def innerPair506Data : WideLogData :=
  { lower := endpoint234
    upper := endpoint235 }

noncomputable def innerPair506Input : RationalEnclosure :=
  { lower := (9768323/16777216), upper := (4975195/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair506Input_eq :
    innerPair506Input = outerEnclosure 24 innerPair506Data.output := by
  rfl'

theorem innerPair506RoundedFacts :
    InnerPairRoundedFacts innerPair506Data innerPair506Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair506Input_eq }

noncomputable def innerPair507Data : WideLogData :=
  { lower := endpoint236
    upper := endpoint241 }

noncomputable def innerPair507Input : RationalEnclosure :=
  { lower := (10228743/16777216), upper := (10441117/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair507Input_eq :
    innerPair507Input = outerEnclosure 24 innerPair507Data.output := by
  rfl'

theorem innerPair507RoundedFacts :
    InnerPairRoundedFacts innerPair507Data innerPair507Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair507Input_eq }

noncomputable def innerPair508Data : WideLogData :=
  { lower := endpoint236
    upper := endpoint247 }

noncomputable def innerPair508Input : RationalEnclosure :=
  { lower := (10228743/16777216), upper := (10789205/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair508Input_eq :
    innerPair508Input = outerEnclosure 24 innerPair508Data.output := by
  rfl'

theorem innerPair508RoundedFacts :
    InnerPairRoundedFacts innerPair508Data innerPair508Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair508Input_eq }

noncomputable def innerPair509Data : WideLogData :=
  { lower := endpoint237
    upper := endpoint242 }

noncomputable def innerPair509Input : RationalEnclosure :=
  { lower := (5167633/8388608), upper := (2645305/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair509Input_eq :
    innerPair509Input = outerEnclosure 24 innerPair509Data.output := by
  rfl'

theorem innerPair509RoundedFacts :
    InnerPairRoundedFacts innerPair509Data innerPair509Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair509Input_eq }

noncomputable def innerPair510Data : WideLogData :=
  { lower := endpoint238
    upper := endpoint242 }

noncomputable def innerPair510Input : RationalEnclosure :=
  { lower := (10370623/16777216), upper := (2645305/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair510Input_eq :
    innerPair510Input = outerEnclosure 24 innerPair510Data.output := by
  rfl'

theorem innerPair510RoundedFacts :
    InnerPairRoundedFacts innerPair510Data innerPair510Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair510Input_eq }

noncomputable def innerPair511Data : WideLogData :=
  { lower := endpoint239
    upper := endpoint240 }

noncomputable def innerPair511Input : RationalEnclosure :=
  { lower := (640409/1048576), upper := (5211761/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair511Input_eq :
    innerPair511Input = outerEnclosure 24 innerPair511Data.output := by
  rfl'

theorem innerPair511RoundedFacts :
    InnerPairRoundedFacts innerPair511Data innerPair511Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair511Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
