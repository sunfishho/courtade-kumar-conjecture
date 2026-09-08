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

noncomputable def innerPair128Data : WideLogData :=
  { lower := endpoint27
    upper := endpoint100 }

noncomputable def innerPair128Input : RationalEnclosure :=
  { lower := (3318965/16777216), upper := (3952143/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair128Input_eq :
    innerPair128Input = outerEnclosure 24 innerPair128Data.output := by
  rfl'

theorem innerPair128RoundedFacts :
    InnerPairRoundedFacts innerPair128Data innerPair128Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair128Input_eq }

noncomputable def innerPair129Data : WideLogData :=
  { lower := endpoint28
    upper := endpoint9 }

noncomputable def innerPair129Input : RationalEnclosure :=
  { lower := (259875/1048576), upper := (595105/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair129Input_eq :
    innerPair129Input = outerEnclosure 24 innerPair129Data.output := by
  rfl'

theorem innerPair129RoundedFacts :
    InnerPairRoundedFacts innerPair129Data innerPair129Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair129Input_eq }

noncomputable def innerPair130Data : WideLogData :=
  { lower := endpoint29
    upper := endpoint30 }

noncomputable def innerPair130Input : RationalEnclosure :=
  { lower := (4361363/16777216), upper := (2575513/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair130Input_eq :
    innerPair130Input = outerEnclosure 24 innerPair130Data.output := by
  rfl'

theorem innerPair130RoundedFacts :
    InnerPairRoundedFacts innerPair130Data innerPair130Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair130Input_eq }

noncomputable def innerPair131Data : WideLogData :=
  { lower := endpoint29
    upper := endpoint37 }

noncomputable def innerPair131Input : RationalEnclosure :=
  { lower := (4361363/16777216), upper := (4957067/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair131Input_eq :
    innerPair131Input = outerEnclosure 24 innerPair131Data.output := by
  rfl'

theorem innerPair131RoundedFacts :
    InnerPairRoundedFacts innerPair131Data innerPair131Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair131Input_eq }

noncomputable def innerPair132Data : WideLogData :=
  { lower := endpoint30
    upper := endpoint34 }

noncomputable def innerPair132Input : RationalEnclosure :=
  { lower := (5151025/16777216), upper := (5532343/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair132Input_eq :
    innerPair132Input = outerEnclosure 24 innerPair132Data.output := by
  rfl'

theorem innerPair132RoundedFacts :
    InnerPairRoundedFacts innerPair132Data innerPair132Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair132Input_eq }

noncomputable def innerPair133Data : WideLogData :=
  { lower := endpoint30
    upper := endpoint38 }

noncomputable def innerPair133Input : RationalEnclosure :=
  { lower := (5151025/16777216), upper := (5719799/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair133Input_eq :
    innerPair133Input = outerEnclosure 24 innerPair133Data.output := by
  rfl'

theorem innerPair133RoundedFacts :
    InnerPairRoundedFacts innerPair133Data innerPair133Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair133Input_eq }

noncomputable def innerPair134Data : WideLogData :=
  { lower := endpoint30
    upper := endpoint42 }

noncomputable def innerPair134Input : RationalEnclosure :=
  { lower := (5151025/16777216), upper := (6449359/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair134Input_eq :
    innerPair134Input = outerEnclosure 24 innerPair134Data.output := by
  rfl'

theorem innerPair134RoundedFacts :
    InnerPairRoundedFacts innerPair134Data innerPair134Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair134Input_eq }

noncomputable def innerPair135Data : WideLogData :=
  { lower := endpoint31
    upper := endpoint26 }

noncomputable def innerPair135Input : RationalEnclosure :=
  { lower := (551871/4194304), upper := (3102483/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair135Input_eq :
    innerPair135Input = outerEnclosure 24 innerPair135Data.output := by
  rfl'

theorem innerPair135RoundedFacts :
    InnerPairRoundedFacts innerPair135Data innerPair135Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair135Input_eq }

noncomputable def innerPair136Data : WideLogData :=
  { lower := endpoint32
    upper := endpoint33 }

noncomputable def innerPair136Input : RationalEnclosure :=
  { lower := (2827889/16777216), upper := (3691217/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair136Input_eq :
    innerPair136Input = outerEnclosure 24 innerPair136Data.output := by
  rfl'

theorem innerPair136RoundedFacts :
    InnerPairRoundedFacts innerPair136Data innerPair136Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair136Input_eq }

noncomputable def innerPair137Data : WideLogData :=
  { lower := endpoint34
    upper := endpoint40 }

noncomputable def innerPair137Input : RationalEnclosure :=
  { lower := (2766171/8388608), upper := (5951213/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair137Input_eq :
    innerPair137Input = outerEnclosure 24 innerPair137Data.output := by
  rfl'

theorem innerPair137RoundedFacts :
    InnerPairRoundedFacts innerPair137Data innerPair137Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair137Input_eq }

noncomputable def innerPair138Data : WideLogData :=
  { lower := endpoint34
    upper := endpoint41 }

noncomputable def innerPair138Input : RationalEnclosure :=
  { lower := (2766171/8388608), upper := (6269921/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair138Input_eq :
    innerPair138Input = outerEnclosure 24 innerPair138Data.output := by
  rfl'

theorem innerPair138RoundedFacts :
    InnerPairRoundedFacts innerPair138Data innerPair138Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair138Input_eq }

noncomputable def innerPair139Data : WideLogData :=
  { lower := endpoint34
    upper := endpoint119 }

noncomputable def innerPair139Input : RationalEnclosure :=
  { lower := (2766171/8388608), upper := (5905185/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair139Input_eq :
    innerPair139Input = outerEnclosure 24 innerPair139Data.output := by
  rfl'

theorem innerPair139RoundedFacts :
    InnerPairRoundedFacts innerPair139Data innerPair139Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair139Input_eq }

noncomputable def innerPair140Data : WideLogData :=
  { lower := endpoint35
    upper := endpoint36 }

noncomputable def innerPair140Input : RationalEnclosure :=
  { lower := (4298077/16777216), upper := (602801/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair140Input_eq :
    innerPair140Input = outerEnclosure 24 innerPair140Data.output := by
  rfl'

theorem innerPair140RoundedFacts :
    InnerPairRoundedFacts innerPair140Data innerPair140Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair140Input_eq }

noncomputable def innerPair141Data : WideLogData :=
  { lower := endpoint35
    upper := endpoint147 }

noncomputable def innerPair141Input : RationalEnclosure :=
  { lower := (4298077/16777216), upper := (4549803/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair141Input_eq :
    innerPair141Input = outerEnclosure 24 innerPair141Data.output := by
  rfl'

theorem innerPair141RoundedFacts :
    InnerPairRoundedFacts innerPair141Data innerPair141Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair141Input_eq }

noncomputable def innerPair142Data : WideLogData :=
  { lower := endpoint37
    upper := endpoint34 }

noncomputable def innerPair142Input : RationalEnclosure :=
  { lower := (2478533/8388608), upper := (5532343/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair142Input_eq :
    innerPair142Input = outerEnclosure 24 innerPair142Data.output := by
  rfl'

theorem innerPair142RoundedFacts :
    InnerPairRoundedFacts innerPair142Data innerPair142Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair142Input_eq }

noncomputable def innerPair143Data : WideLogData :=
  { lower := endpoint37
    upper := endpoint38 }

noncomputable def innerPair143Input : RationalEnclosure :=
  { lower := (2478533/8388608), upper := (5719799/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair143Input_eq :
    innerPair143Input = outerEnclosure 24 innerPair143Data.output := by
  rfl'

theorem innerPair143RoundedFacts :
    InnerPairRoundedFacts innerPair143Data innerPair143Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair143Input_eq }

noncomputable def innerPair144Data : WideLogData :=
  { lower := endpoint38
    upper := endpoint41 }

noncomputable def innerPair144Input : RationalEnclosure :=
  { lower := (2859899/8388608), upper := (6269921/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair144Input_eq :
    innerPair144Input = outerEnclosure 24 innerPair144Data.output := by
  rfl'

theorem innerPair144RoundedFacts :
    InnerPairRoundedFacts innerPair144Data innerPair144Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair144Input_eq }

noncomputable def innerPair145Data : WideLogData :=
  { lower := endpoint38
    upper := endpoint42 }

noncomputable def innerPair145Input : RationalEnclosure :=
  { lower := (2859899/8388608), upper := (6449359/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair145Input_eq :
    innerPair145Input = outerEnclosure 24 innerPair145Data.output := by
  rfl'

theorem innerPair145RoundedFacts :
    InnerPairRoundedFacts innerPair145Data innerPair145Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair145Input_eq }

noncomputable def innerPair146Data : WideLogData :=
  { lower := endpoint38
    upper := endpoint156 }

noncomputable def innerPair146Input : RationalEnclosure :=
  { lower := (2859899/8388608), upper := (5997115/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair146Input_eq :
    innerPair146Input = outerEnclosure 24 innerPair146Data.output := by
  rfl'

theorem innerPair146RoundedFacts :
    InnerPairRoundedFacts innerPair146Data innerPair146Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair146Input_eq }

noncomputable def innerPair147Data : WideLogData :=
  { lower := endpoint39
    upper := endpoint40 }

noncomputable def innerPair147Input : RationalEnclosure :=
  { lower := (2695181/8388608), upper := (5951213/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair147Input_eq :
    innerPair147Input = outerEnclosure 24 innerPair147Data.output := by
  rfl'

theorem innerPair147RoundedFacts :
    InnerPairRoundedFacts innerPair147Data innerPair147Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair147Input_eq }

noncomputable def innerPair148Data : WideLogData :=
  { lower := endpoint41
    upper := endpoint49 }

noncomputable def innerPair148Input : RationalEnclosure :=
  { lower := (195935/524288), upper := (6976435/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair148Input_eq :
    innerPair148Input = outerEnclosure 24 innerPair148Data.output := by
  rfl'

theorem innerPair148RoundedFacts :
    InnerPairRoundedFacts innerPair148Data innerPair148Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair148Input_eq }

noncomputable def innerPair149Data : WideLogData :=
  { lower := endpoint41
    upper := endpoint120 }

noncomputable def innerPair149Input : RationalEnclosure :=
  { lower := (195935/524288), upper := (6626897/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair149Input_eq :
    innerPair149Input = outerEnclosure 24 innerPair149Data.output := by
  rfl'

theorem innerPair149RoundedFacts :
    InnerPairRoundedFacts innerPair149Data innerPair149Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair149Input_eq }

noncomputable def innerPair150Data : WideLogData :=
  { lower := endpoint41
    upper := endpoint190 }

noncomputable def innerPair150Input : RationalEnclosure :=
  { lower := (195935/524288), upper := (6538363/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair150Input_eq :
    innerPair150Input = outerEnclosure 24 innerPair150Data.output := by
  rfl'

theorem innerPair150RoundedFacts :
    InnerPairRoundedFacts innerPair150Data innerPair150Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair150Input_eq }

noncomputable def innerPair151Data : WideLogData :=
  { lower := endpoint42
    upper := endpoint19 }

noncomputable def innerPair151Input : RationalEnclosure :=
  { lower := (3224679/8388608), upper := (3574255/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair151Input_eq :
    innerPair151Input = outerEnclosure 24 innerPair151Data.output := by
  rfl'

theorem innerPair151RoundedFacts :
    InnerPairRoundedFacts innerPair151Data innerPair151Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair151Input_eq }

noncomputable def innerPair152Data : WideLogData :=
  { lower := endpoint42
    upper := endpoint43 }

noncomputable def innerPair152Input : RationalEnclosure :=
  { lower := (3224679/8388608), upper := (7318839/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair152Input_eq :
    innerPair152Input = outerEnclosure 24 innerPair152Data.output := by
  rfl'

theorem innerPair152RoundedFacts :
    InnerPairRoundedFacts innerPair152Data innerPair152Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair152Input_eq }

noncomputable def innerPair153Data : WideLogData :=
  { lower := endpoint42
    upper := endpoint49 }

noncomputable def innerPair153Input : RationalEnclosure :=
  { lower := (3224679/8388608), upper := (6976435/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair153Input_eq :
    innerPair153Input = outerEnclosure 24 innerPair153Data.output := by
  rfl'

theorem innerPair153RoundedFacts :
    InnerPairRoundedFacts innerPair153Data innerPair153Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair153Input_eq }

noncomputable def innerPair154Data : WideLogData :=
  { lower := endpoint43
    upper := endpoint44 }

noncomputable def innerPair154Input : RationalEnclosure :=
  { lower := (3659419/8388608), upper := (7819689/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair154Input_eq :
    innerPair154Input = outerEnclosure 24 innerPair154Data.output := by
  rfl'

theorem innerPair154RoundedFacts :
    InnerPairRoundedFacts innerPair154Data innerPair154Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair154Input_eq }

noncomputable def innerPair155Data : WideLogData :=
  { lower := endpoint43
    upper := endpoint45 }

noncomputable def innerPair155Input : RationalEnclosure :=
  { lower := (3659419/8388608), upper := (8306019/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair155Input_eq :
    innerPair155Input = outerEnclosure 24 innerPair155Data.output := by
  rfl'

theorem innerPair155RoundedFacts :
    InnerPairRoundedFacts innerPair155Data innerPair155Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair155Input_eq }

noncomputable def innerPair156Data : WideLogData :=
  { lower := endpoint43
    upper := endpoint47 }

noncomputable def innerPair156Input : RationalEnclosure :=
  { lower := (3659419/8388608), upper := (3827197/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair156Input_eq :
    innerPair156Input = outerEnclosure 24 innerPair156Data.output := by
  rfl'

theorem innerPair156RoundedFacts :
    InnerPairRoundedFacts innerPair156Data innerPair156Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair156Input_eq }

noncomputable def innerPair157Data : WideLogData :=
  { lower := endpoint44
    upper := endpoint45 }

noncomputable def innerPair157Input : RationalEnclosure :=
  { lower := (977461/2097152), upper := (8306019/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair157Input_eq :
    innerPair157Input = outerEnclosure 24 innerPair157Data.output := by
  rfl'

theorem innerPair157RoundedFacts :
    InnerPairRoundedFacts innerPair157Data innerPair157Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair157Input_eq }

noncomputable def innerPair158Data : WideLogData :=
  { lower := endpoint44
    upper := endpoint48 }

noncomputable def innerPair158Input : RationalEnclosure :=
  { lower := (977461/2097152), upper := (4232523/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair158Input_eq :
    innerPair158Input = outerEnclosure 24 innerPair158Data.output := by
  rfl'

theorem innerPair158RoundedFacts :
    InnerPairRoundedFacts innerPair158Data innerPair158Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair158Input_eq }

noncomputable def innerPair159Data : WideLogData :=
  { lower := endpoint44
    upper := endpoint166 }

noncomputable def innerPair159Input : RationalEnclosure :=
  { lower := (977461/2097152), upper := (1008077/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair159Input_eq :
    innerPair159Input = outerEnclosure 24 innerPair159Data.output := by
  rfl'

theorem innerPair159RoundedFacts :
    InnerPairRoundedFacts innerPair159Data innerPair159Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair159Input_eq }

noncomputable def innerPair160Data : WideLogData :=
  { lower := endpoint45
    upper := endpoint20 }

noncomputable def innerPair160Input : RationalEnclosure :=
  { lower := (4153009/8388608), upper := (8933277/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair160Input_eq :
    innerPair160Input = outerEnclosure 24 innerPair160Data.output := by
  rfl'

theorem innerPair160RoundedFacts :
    InnerPairRoundedFacts innerPair160Data innerPair160Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair160Input_eq }

noncomputable def innerPair161Data : WideLogData :=
  { lower := endpoint45
    upper := endpoint56 }

noncomputable def innerPair161Input : RationalEnclosure :=
  { lower := (4153009/8388608), upper := (8661733/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair161Input_eq :
    innerPair161Input = outerEnclosure 24 innerPair161Data.output := by
  rfl'

theorem innerPair161RoundedFacts :
    InnerPairRoundedFacts innerPair161Data innerPair161Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair161Input_eq }

noncomputable def innerPair162Data : WideLogData :=
  { lower := endpoint45
    upper := endpoint62 }

noncomputable def innerPair162Input : RationalEnclosure :=
  { lower := (4153009/8388608), upper := (9086495/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair162Input_eq :
    innerPair162Input = outerEnclosure 24 innerPair162Data.output := by
  rfl'

theorem innerPair162RoundedFacts :
    InnerPairRoundedFacts innerPair162Data innerPair162Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair162Input_eq }

noncomputable def innerPair163Data : WideLogData :=
  { lower := endpoint45
    upper := endpoint133 }

noncomputable def innerPair163Input : RationalEnclosure :=
  { lower := (4153009/8388608), upper := (8622579/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair163Input_eq :
    innerPair163Input = outerEnclosure 24 innerPair163Data.output := by
  rfl'

theorem innerPair163RoundedFacts :
    InnerPairRoundedFacts innerPair163Data innerPair163Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair163Input_eq }

noncomputable def innerPair164Data : WideLogData :=
  { lower := endpoint45
    upper := endpoint134 }

noncomputable def innerPair164Input : RationalEnclosure :=
  { lower := (4153009/8388608), upper := (1063071/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair164Input_eq :
    innerPair164Input = outerEnclosure 24 innerPair164Data.output := by
  rfl'

theorem innerPair164RoundedFacts :
    InnerPairRoundedFacts innerPair164Data innerPair164Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair164Input_eq }

noncomputable def innerPair165Data : WideLogData :=
  { lower := endpoint45
    upper := endpoint199 }

noncomputable def innerPair165Input : RationalEnclosure :=
  { lower := (4153009/8388608), upper := (8543997/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair165Input_eq :
    innerPair165Input = outerEnclosure 24 innerPair165Data.output := by
  rfl'

theorem innerPair165RoundedFacts :
    InnerPairRoundedFacts innerPair165Data innerPair165Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair165Input_eq }

noncomputable def innerPair166Data : WideLogData :=
  { lower := endpoint46
    upper := endpoint45 }

noncomputable def innerPair166Input : RationalEnclosure :=
  { lower := (7983369/16777216), upper := (8306019/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair166Input_eq :
    innerPair166Input = outerEnclosure 24 innerPair166Data.output := by
  rfl'

theorem innerPair166RoundedFacts :
    InnerPairRoundedFacts innerPair166Data innerPair166Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair166Input_eq }

noncomputable def innerPair167Data : WideLogData :=
  { lower := endpoint46
    upper := endpoint48 }

noncomputable def innerPair167Input : RationalEnclosure :=
  { lower := (7983369/16777216), upper := (4232523/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair167Input_eq :
    innerPair167Input = outerEnclosure 24 innerPair167Data.output := by
  rfl'

theorem innerPair167RoundedFacts :
    InnerPairRoundedFacts innerPair167Data innerPair167Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair167Input_eq }

noncomputable def innerPair168Data : WideLogData :=
  { lower := endpoint46
    upper := endpoint133 }

noncomputable def innerPair168Input : RationalEnclosure :=
  { lower := (7983369/16777216), upper := (8622579/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair168Input_eq :
    innerPair168Input = outerEnclosure 24 innerPair168Data.output := by
  rfl'

theorem innerPair168RoundedFacts :
    InnerPairRoundedFacts innerPair168Data innerPair168Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair168Input_eq }

noncomputable def innerPair169Data : WideLogData :=
  { lower := endpoint47
    upper := endpoint20 }

noncomputable def innerPair169Input : RationalEnclosure :=
  { lower := (7654393/16777216), upper := (8933277/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair169Input_eq :
    innerPair169Input = outerEnclosure 24 innerPair169Data.output := by
  rfl'

theorem innerPair169RoundedFacts :
    InnerPairRoundedFacts innerPair169Data innerPair169Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair169Input_eq }

noncomputable def innerPair170Data : WideLogData :=
  { lower := endpoint47
    upper := endpoint45 }

noncomputable def innerPair170Input : RationalEnclosure :=
  { lower := (7654393/16777216), upper := (8306019/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair170Input_eq :
    innerPair170Input = outerEnclosure 24 innerPair170Data.output := by
  rfl'

theorem innerPair170RoundedFacts :
    InnerPairRoundedFacts innerPair170Data innerPair170Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair170Input_eq }

noncomputable def innerPair171Data : WideLogData :=
  { lower := endpoint47
    upper := endpoint46 }

noncomputable def innerPair171Input : RationalEnclosure :=
  { lower := (7654393/16777216), upper := (3991685/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair171Input_eq :
    innerPair171Input = outerEnclosure 24 innerPair171Data.output := by
  rfl'

theorem innerPair171RoundedFacts :
    InnerPairRoundedFacts innerPair171Data innerPair171Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair171Input_eq }

noncomputable def innerPair172Data : WideLogData :=
  { lower := endpoint47
    upper := endpoint48 }

noncomputable def innerPair172Input : RationalEnclosure :=
  { lower := (7654393/16777216), upper := (4232523/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair172Input_eq :
    innerPair172Input = outerEnclosure 24 innerPair172Data.output := by
  rfl'

theorem innerPair172RoundedFacts :
    InnerPairRoundedFacts innerPair172Data innerPair172Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair172Input_eq }

noncomputable def innerPair173Data : WideLogData :=
  { lower := endpoint48
    upper := endpoint20 }

noncomputable def innerPair173Input : RationalEnclosure :=
  { lower := (8465045/16777216), upper := (8933277/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair173Input_eq :
    innerPair173Input = outerEnclosure 24 innerPair173Data.output := by
  rfl'

theorem innerPair173RoundedFacts :
    InnerPairRoundedFacts innerPair173Data innerPair173Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair173Input_eq }

noncomputable def innerPair174Data : WideLogData :=
  { lower := endpoint48
    upper := endpoint59 }

noncomputable def innerPair174Input : RationalEnclosure :=
  { lower := (8465045/16777216), upper := (8700795/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair174Input_eq :
    innerPair174Input = outerEnclosure 24 innerPair174Data.output := by
  rfl'

theorem innerPair174RoundedFacts :
    InnerPairRoundedFacts innerPair174Data innerPair174Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair174Input_eq }

noncomputable def innerPair175Data : WideLogData :=
  { lower := endpoint48
    upper := endpoint62 }

noncomputable def innerPair175Input : RationalEnclosure :=
  { lower := (8465045/16777216), upper := (9086495/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair175Input_eq :
    innerPair175Input = outerEnclosure 24 innerPair175Data.output := by
  rfl'

theorem innerPair175RoundedFacts :
    InnerPairRoundedFacts innerPair175Data innerPair175Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair175Input_eq }

noncomputable def innerPair176Data : WideLogData :=
  { lower := endpoint49
    upper := endpoint19 }

noncomputable def innerPair176Input : RationalEnclosure :=
  { lower := (3488217/8388608), upper := (3574255/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair176Input_eq :
    innerPair176Input = outerEnclosure 24 innerPair176Data.output := by
  rfl'

theorem innerPair176RoundedFacts :
    InnerPairRoundedFacts innerPair176Data innerPair176Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair176Input_eq }

noncomputable def innerPair177Data : WideLogData :=
  { lower := endpoint49
    upper := endpoint43 }

noncomputable def innerPair177Input : RationalEnclosure :=
  { lower := (3488217/8388608), upper := (7318839/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair177Input_eq :
    innerPair177Input = outerEnclosure 24 innerPair177Data.output := by
  rfl'

theorem innerPair177RoundedFacts :
    InnerPairRoundedFacts innerPair177Data innerPair177Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair177Input_eq }

noncomputable def innerPair178Data : WideLogData :=
  { lower := endpoint49
    upper := endpoint47 }

noncomputable def innerPair178Input : RationalEnclosure :=
  { lower := (3488217/8388608), upper := (3827197/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair178Input_eq :
    innerPair178Input = outerEnclosure 24 innerPair178Data.output := by
  rfl'

theorem innerPair178RoundedFacts :
    InnerPairRoundedFacts innerPair178Data innerPair178Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair178Input_eq }

noncomputable def innerPair179Data : WideLogData :=
  { lower := endpoint49
    upper := endpoint52 }

noncomputable def innerPair179Input : RationalEnclosure :=
  { lower := (3488217/8388608), upper := (3764673/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair179Input_eq :
    innerPair179Input = outerEnclosure 24 innerPair179Data.output := by
  rfl'

theorem innerPair179RoundedFacts :
    InnerPairRoundedFacts innerPair179Data innerPair179Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair179Input_eq }

noncomputable def innerPair180Data : WideLogData :=
  { lower := endpoint50
    upper := endpoint51 }

noncomputable def innerPair180Input : RationalEnclosure :=
  { lower := (3351991/8388608), upper := (3611621/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair180Input_eq :
    innerPair180Input = outerEnclosure 24 innerPair180Data.output := by
  rfl'

theorem innerPair180RoundedFacts :
    InnerPairRoundedFacts innerPair180Data innerPair180Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair180Input_eq }

noncomputable def innerPair181Data : WideLogData :=
  { lower := endpoint52
    upper := endpoint168 }

noncomputable def innerPair181Input : RationalEnclosure :=
  { lower := (7529345/16777216), upper := (7737245/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair181Input_eq :
    innerPair181Input = outerEnclosure 24 innerPair181Data.output := by
  rfl'

theorem innerPair181RoundedFacts :
    InnerPairRoundedFacts innerPair181Data innerPair181Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair181Input_eq }

noncomputable def innerPair182Data : WideLogData :=
  { lower := endpoint53
    upper := endpoint52 }

noncomputable def innerPair182Input : RationalEnclosure :=
  { lower := (3638209/8388608), upper := (3764673/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair182Input_eq :
    innerPair182Input = outerEnclosure 24 innerPair182Data.output := by
  rfl'

theorem innerPair182RoundedFacts :
    InnerPairRoundedFacts innerPair182Data innerPair182Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair182Input_eq }

noncomputable def innerPair183Data : WideLogData :=
  { lower := endpoint53
    upper := endpoint54 }

noncomputable def innerPair183Input : RationalEnclosure :=
  { lower := (3638209/8388608), upper := (7860759/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair183Input_eq :
    innerPair183Input = outerEnclosure 24 innerPair183Data.output := by
  rfl'

theorem innerPair183RoundedFacts :
    InnerPairRoundedFacts innerPair183Data innerPair183Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair183Input_eq }

noncomputable def innerPair184Data : WideLogData :=
  { lower := endpoint53
    upper := endpoint127 }

noncomputable def innerPair184Input : RationalEnclosure :=
  { lower := (3638209/8388608), upper := (7612815/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair184Input_eq :
    innerPair184Input = outerEnclosure 24 innerPair184Data.output := by
  rfl'

theorem innerPair184RoundedFacts :
    InnerPairRoundedFacts innerPair184Data innerPair184Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair184Input_eq }

noncomputable def innerPair185Data : WideLogData :=
  { lower := endpoint54
    upper := endpoint55 }

noncomputable def innerPair185Input : RationalEnclosure :=
  { lower := (3930379/8388608), upper := (2026273/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair185Input_eq :
    innerPair185Input = outerEnclosure 24 innerPair185Data.output := by
  rfl'

theorem innerPair185RoundedFacts :
    InnerPairRoundedFacts innerPair185Data innerPair185Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair185Input_eq }

noncomputable def innerPair186Data : WideLogData :=
  { lower := endpoint54
    upper := endpoint126 }

noncomputable def innerPair186Input : RationalEnclosure :=
  { lower := (3930379/8388608), upper := (8185751/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair186Input_eq :
    innerPair186Input = outerEnclosure 24 innerPair186Data.output := by
  rfl'

theorem innerPair186RoundedFacts :
    InnerPairRoundedFacts innerPair186Data innerPair186Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair186Input_eq }

noncomputable def innerPair187Data : WideLogData :=
  { lower := endpoint55
    upper := endpoint56 }

noncomputable def innerPair187Input : RationalEnclosure :=
  { lower := (8105091/16777216), upper := (8661733/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair187Input_eq :
    innerPair187Input = outerEnclosure 24 innerPair187Data.output := by
  rfl'

theorem innerPair187RoundedFacts :
    InnerPairRoundedFacts innerPair187Data innerPair187Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair187Input_eq }

noncomputable def innerPair188Data : WideLogData :=
  { lower := endpoint55
    upper := endpoint171 }

noncomputable def innerPair188Input : RationalEnclosure :=
  { lower := (8105091/16777216), upper := (8345917/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair188Input_eq :
    innerPair188Input = outerEnclosure 24 innerPair188Data.output := by
  rfl'

theorem innerPair188RoundedFacts :
    InnerPairRoundedFacts innerPair188Data innerPair188Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair188Input_eq }

noncomputable def innerPair189Data : WideLogData :=
  { lower := endpoint56
    upper := endpoint136 }

noncomputable def innerPair189Input : RationalEnclosure :=
  { lower := (2165433/4194304), upper := (8971713/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair189Input_eq :
    innerPair189Input = outerEnclosure 24 innerPair189Data.output := by
  rfl'

theorem innerPair189RoundedFacts :
    InnerPairRoundedFacts innerPair189Data innerPair189Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair189Input_eq }

noncomputable def innerPair190Data : WideLogData :=
  { lower := endpoint56
    upper := endpoint137 }

noncomputable def innerPair190Input : RationalEnclosure :=
  { lower := (2165433/4194304), upper := (8856141/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair190Input_eq :
    innerPair190Input = outerEnclosure 24 innerPair190Data.output := by
  rfl'

theorem innerPair190RoundedFacts :
    InnerPairRoundedFacts innerPair190Data innerPair190Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair190Input_eq }

noncomputable def innerPair191Data : WideLogData :=
  { lower := endpoint56
    upper := endpoint138 }

noncomputable def innerPair191Input : RationalEnclosure :=
  { lower := (2165433/4194304), upper := (4581291/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair191Input_eq :
    innerPair191Input = outerEnclosure 24 innerPair191Data.output := by
  rfl'

theorem innerPair191RoundedFacts :
    InnerPairRoundedFacts innerPair191Data innerPair191Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair191Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
