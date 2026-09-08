import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
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

noncomputable def innerPair832Data : WideLogData :=
  { lower := endpoint527
    upper := endpoint492 }

noncomputable def innerPair832Input : RationalEnclosure :=
  { lower := (9431485/8388608), upper := (19283475/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair832Input_eq :
    innerPair832Input = outerEnclosure 24 innerPair832Data.output := by
  rfl'

theorem innerPair832RoundedFacts :
    InnerPairRoundedFacts innerPair832Data innerPair832Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair832Input_eq }

noncomputable def innerPair833Data : WideLogData :=
  { lower := endpoint527
    upper := endpoint531 }

noncomputable def innerPair833Input : RationalEnclosure :=
  { lower := (9431485/8388608), upper := (9693487/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair833Input_eq :
    innerPair833Input = outerEnclosure 24 innerPair833Data.output := by
  rfl'

theorem innerPair833RoundedFacts :
    InnerPairRoundedFacts innerPair833Data innerPair833Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair833Input_eq }

noncomputable def innerPair834Data : WideLogData :=
  { lower := endpoint528
    upper := endpoint535 }

noncomputable def innerPair834Input : RationalEnclosure :=
  { lower := (4800053/4194304), upper := (9806225/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair834Input_eq :
    innerPair834Input = outerEnclosure 24 innerPair834Data.output := by
  rfl'

theorem innerPair834RoundedFacts :
    InnerPairRoundedFacts innerPair834Data innerPair834Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair834Input_eq }

noncomputable def innerPair835Data : WideLogData :=
  { lower := endpoint530
    upper := endpoint494 }

noncomputable def innerPair835Input : RationalEnclosure :=
  { lower := (9473959/8388608), upper := (19530809/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair835Input_eq :
    innerPair835Input = outerEnclosure 24 innerPair835Data.output := by
  rfl'

theorem innerPair835RoundedFacts :
    InnerPairRoundedFacts innerPair835Data innerPair835Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair835Input_eq }

noncomputable def innerPair836Data : WideLogData :=
  { lower := endpoint530
    upper := endpoint532 }

noncomputable def innerPair836Input : RationalEnclosure :=
  { lower := (9473959/8388608), upper := (19366325/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair836Input_eq :
    innerPair836Input = outerEnclosure 24 innerPair836Data.output := by
  rfl'

theorem innerPair836RoundedFacts :
    InnerPairRoundedFacts innerPair836Data innerPair836Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair836Input_eq }

noncomputable def innerPair837Data : WideLogData :=
  { lower := endpoint532
    upper := endpoint533 }

noncomputable def innerPair837Input : RationalEnclosure :=
  { lower := (4841581/4194304), upper := (19875073/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair837Input_eq :
    innerPair837Input = outerEnclosure 24 innerPair837Data.output := by
  rfl'

theorem innerPair837RoundedFacts :
    InnerPairRoundedFacts innerPair837Data innerPair837Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair837Input_eq }

noncomputable def innerPair838Data : WideLogData :=
  { lower := endpoint532
    upper := endpoint534 }

noncomputable def innerPair838Input : RationalEnclosure :=
  { lower := (4841581/4194304), upper := (19935099/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair838Input_eq :
    innerPair838Input = outerEnclosure 24 innerPair838Data.output := by
  rfl'

theorem innerPair838RoundedFacts :
    InnerPairRoundedFacts innerPair838Data innerPair838Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair838Input_eq }

noncomputable def innerPair839Data : WideLogData :=
  { lower := endpoint533
    upper := endpoint558 }

noncomputable def innerPair839Input : RationalEnclosure :=
  { lower := (77637/65536), upper := (20232049/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair839Input_eq :
    innerPair839Input = outerEnclosure 24 innerPair839Data.output := by
  rfl'

theorem innerPair839RoundedFacts :
    InnerPairRoundedFacts innerPair839Data innerPair839Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair839Input_eq }

noncomputable def innerPair840Data : WideLogData :=
  { lower := endpoint535
    upper := endpoint495 }

noncomputable def innerPair840Input : RationalEnclosure :=
  { lower := (19612449/16777216), upper := (5062915/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair840Input_eq :
    innerPair840Input = outerEnclosure 24 innerPair840Data.output := by
  rfl'

theorem innerPair840RoundedFacts :
    InnerPairRoundedFacts innerPair840Data innerPair840Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair840Input_eq }

noncomputable def innerPair841Data : WideLogData :=
  { lower := endpoint535
    upper := endpoint536 }

noncomputable def innerPair841Input : RationalEnclosure :=
  { lower := (19612449/16777216), upper := (10086539/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair841Input_eq :
    innerPair841Input = outerEnclosure 24 innerPair841Data.output := by
  rfl'

theorem innerPair841RoundedFacts :
    InnerPairRoundedFacts innerPair841Data innerPair841Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair841Input_eq }

noncomputable def innerPair842Data : WideLogData :=
  { lower := endpoint536
    upper := endpoint540 }

noncomputable def innerPair842Input : RationalEnclosure :=
  { lower := (5043269/4194304), upper := (10281179/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair842Input_eq :
    innerPair842Input = outerEnclosure 24 innerPair842Data.output := by
  rfl'

theorem innerPair842RoundedFacts :
    InnerPairRoundedFacts innerPair842Data innerPair842Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair842Input_eq }

noncomputable def innerPair843Data : WideLogData :=
  { lower := endpoint537
    upper := endpoint538 }

noncomputable def innerPair843Input : RationalEnclosure :=
  { lower := (9897351/8388608), upper := (20290813/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair843Input_eq :
    innerPair843Input = outerEnclosure 24 innerPair843Data.output := by
  rfl'

theorem innerPair843RoundedFacts :
    InnerPairRoundedFacts innerPair843Data innerPair843Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair843Input_eq }

noncomputable def innerPair844Data : WideLogData :=
  { lower := endpoint539
    upper := endpoint540 }

noncomputable def innerPair844Input : RationalEnclosure :=
  { lower := (1250925/1048576), upper := (10281179/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair844Input_eq :
    innerPair844Input = outerEnclosure 24 innerPair844Data.output := by
  rfl'

theorem innerPair844RoundedFacts :
    InnerPairRoundedFacts innerPair844Data innerPair844Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair844Input_eq }

noncomputable def innerPair845Data : WideLogData :=
  { lower := endpoint540
    upper := endpoint543 }

noncomputable def innerPair845Input : RationalEnclosure :=
  { lower := (5140589/4194304), upper := (21092607/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair845Input_eq :
    innerPair845Input = outerEnclosure 24 innerPair845Data.output := by
  rfl'

theorem innerPair845RoundedFacts :
    InnerPairRoundedFacts innerPair845Data innerPair845Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair845Input_eq }

noncomputable def innerPair846Data : WideLogData :=
  { lower := endpoint541
    upper := endpoint542 }

noncomputable def innerPair846Input : RationalEnclosure :=
  { lower := (10164937/8388608), upper := (10433703/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair846Input_eq :
    innerPair846Input = outerEnclosure 24 innerPair846Data.output := by
  rfl'

theorem innerPair846RoundedFacts :
    InnerPairRoundedFacts innerPair846Data innerPair846Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair846Input_eq }

noncomputable def innerPair847Data : WideLogData :=
  { lower := endpoint541
    upper := endpoint559 }

noncomputable def innerPair847Input : RationalEnclosure :=
  { lower := (10164937/8388608), upper := (20791663/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair847Input_eq :
    innerPair847Input = outerEnclosure 24 innerPair847Data.output := by
  rfl'

theorem innerPair847RoundedFacts :
    InnerPairRoundedFacts innerPair847Data innerPair847Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair847Input_eq }

noncomputable def innerPair848Data : WideLogData :=
  { lower := endpoint542
    upper := endpoint544 }

noncomputable def innerPair848Input : RationalEnclosure :=
  { lower := (20867405/16777216), upper := (21388249/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair848Input_eq :
    innerPair848Input = outerEnclosure 24 innerPair848Data.output := by
  rfl'

theorem innerPair848RoundedFacts :
    InnerPairRoundedFacts innerPair848Data innerPair848Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair848Input_eq }

noncomputable def innerPair849Data : WideLogData :=
  { lower := endpoint544
    upper := endpoint566 }

noncomputable def innerPair849Input : RationalEnclosure :=
  { lower := (21388247/16777216), upper := (21964347/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair849Input_eq :
    innerPair849Input = outerEnclosure 24 innerPair849Data.output := by
  rfl'

theorem innerPair849RoundedFacts :
    InnerPairRoundedFacts innerPair849Data innerPair849Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair849Input_eq }

noncomputable def innerPair850Data : WideLogData :=
  { lower := endpoint545
    upper := endpoint546 }

noncomputable def innerPair850Input : RationalEnclosure :=
  { lower := (9116943/8388608), upper := (18627121/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair850Input_eq :
    innerPair850Input = outerEnclosure 24 innerPair850Data.output := by
  rfl'

theorem innerPair850RoundedFacts :
    InnerPairRoundedFacts innerPair850Data innerPair850Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair850Input_eq }

noncomputable def innerPair851Data : WideLogData :=
  { lower := endpoint549
    upper := endpoint550 }

noncomputable def innerPair851Input : RationalEnclosure :=
  { lower := (9321653/8388608), upper := (9500397/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair851Input_eq :
    innerPair851Input = outerEnclosure 24 innerPair851Data.output := by
  rfl'

theorem innerPair851RoundedFacts :
    InnerPairRoundedFacts innerPair851Data innerPair851Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair851Input_eq }

noncomputable def innerPair852Data : WideLogData :=
  { lower := endpoint551
    upper := endpoint552 }

noncomputable def innerPair852Input : RationalEnclosure :=
  { lower := (18798975/16777216), upper := (19158427/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair852Input_eq :
    innerPair852Input = outerEnclosure 24 innerPair852Data.output := by
  rfl'

theorem innerPair852RoundedFacts :
    InnerPairRoundedFacts innerPair852Data innerPair852Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair852Input_eq }

noncomputable def innerPair853Data : WideLogData :=
  { lower := endpoint553
    upper := endpoint494 }

noncomputable def innerPair853Input : RationalEnclosure :=
  { lower := (9516219/8388608), upper := (19530809/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair853Input_eq :
    innerPair853Input = outerEnclosure 24 innerPair853Data.output := by
  rfl'

theorem innerPair853RoundedFacts :
    InnerPairRoundedFacts innerPair853Data innerPair853Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair853Input_eq }

noncomputable def innerPair854Data : WideLogData :=
  { lower := endpoint556
    upper := endpoint557 }

noncomputable def innerPair854Input : RationalEnclosure :=
  { lower := (4918355/4194304), upper := (20034667/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair854Input_eq :
    innerPair854Input = outerEnclosure 24 innerPair854Data.output := by
  rfl'

theorem innerPair854RoundedFacts :
    InnerPairRoundedFacts innerPair854Data innerPair854Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair854Input_eq }

noncomputable def innerPair855Data : WideLogData :=
  { lower := endpoint561
    upper := endpoint562 }

noncomputable def innerPair855Input : RationalEnclosure :=
  { lower := (2617851/2097152), upper := (2682669/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair855Input_eq :
    innerPair855Input = outerEnclosure 24 innerPair855Data.output := by
  rfl'

theorem innerPair855RoundedFacts :
    InnerPairRoundedFacts innerPair855Data innerPair855Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair855Input_eq }

noncomputable def innerPair856Data : WideLogData :=
  { lower := endpoint561
    upper := endpoint568 }

noncomputable def innerPair856Input : RationalEnclosure :=
  { lower := (2617851/2097152), upper := (21678771/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair856Input_eq :
    innerPair856Input = outerEnclosure 24 innerPair856Data.output := by
  rfl'

theorem innerPair856RoundedFacts :
    InnerPairRoundedFacts innerPair856Data innerPair856Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair856Input_eq }

noncomputable def innerPair857Data : WideLogData :=
  { lower := endpoint562
    upper := endpoint567 }

noncomputable def innerPair857Input : RationalEnclosure :=
  { lower := (21461351/16777216), upper := (5508747/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair857Input_eq :
    innerPair857Input = outerEnclosure 24 innerPair857Data.output := by
  rfl'

theorem innerPair857RoundedFacts :
    InnerPairRoundedFacts innerPair857Data innerPair857Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair857Input_eq }

noncomputable def innerPair858Data : WideLogData :=
  { lower := endpoint564
    upper := endpoint565 }

noncomputable def innerPair858Input : RationalEnclosure :=
  { lower := (10620539/8388608), upper := (10875311/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair858Input_eq :
    innerPair858Input = outerEnclosure 24 innerPair858Data.output := by
  rfl'

theorem innerPair858RoundedFacts :
    InnerPairRoundedFacts innerPair858Data innerPair858Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair858Input_eq }

noncomputable def innerPair859Data : WideLogData :=
  { lower := endpoint568
    upper := endpoint569 }

noncomputable def innerPair859Input : RationalEnclosure :=
  { lower := (21678769/16777216), upper := (2780643/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair859Input_eq :
    innerPair859Input = outerEnclosure 24 innerPair859Data.output := by
  rfl'

theorem innerPair859RoundedFacts :
    InnerPairRoundedFacts innerPair859Data innerPair859Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair859Input_eq }

noncomputable def innerPair860Data : WideLogData :=
  { lower := endpoint570
    upper := endpoint571 }

noncomputable def innerPair860Input : RationalEnclosure :=
  { lower := (21857823/16777216), upper := (11165969/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair860Input_eq :
    innerPair860Input = outerEnclosure 24 innerPair860Data.output := by
  rfl'

theorem innerPair860RoundedFacts :
    InnerPairRoundedFacts innerPair860Data innerPair860Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair860Input_eq }

noncomputable def innerPair861Data : WideLogData :=
  { lower := endpoint572
    upper := endpoint573 }

noncomputable def innerPair861Input : RationalEnclosure :=
  { lower := (5526333/4194304), upper := (22657719/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair861Input_eq :
    innerPair861Input = outerEnclosure 24 innerPair861Data.output := by
  rfl'

theorem innerPair861RoundedFacts :
    InnerPairRoundedFacts innerPair861Data innerPair861Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair861Input_eq }

noncomputable def innerPair862Data : WideLogData :=
  { lower := endpoint572
    upper := endpoint581 }

noncomputable def innerPair862Input : RationalEnclosure :=
  { lower := (5526333/4194304), upper := (2857533/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair862Input_eq :
    innerPair862Input = outerEnclosure 24 innerPair862Data.output := by
  rfl'

theorem innerPair862RoundedFacts :
    InnerPairRoundedFacts innerPair862Data innerPair862Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair862Input_eq }

noncomputable def innerPair863Data : WideLogData :=
  { lower := endpoint574
    upper := endpoint575 }

noncomputable def innerPair863Input : RationalEnclosure :=
  { lower := (11157307/8388608), upper := (89101/65536) }

set_option maxRecDepth 1000000 in
private theorem innerPair863Input_eq :
    innerPair863Input = outerEnclosure 24 innerPair863Data.output := by
  rfl'

theorem innerPair863RoundedFacts :
    InnerPairRoundedFacts innerPair863Data innerPair863Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair863Input_eq }

noncomputable def innerPair864Data : WideLogData :=
  { lower := endpoint574
    upper := endpoint577 }

noncomputable def innerPair864Input : RationalEnclosure :=
  { lower := (11157307/8388608), upper := (2882549/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair864Input_eq :
    innerPair864Input = outerEnclosure 24 innerPair864Data.output := by
  rfl'

theorem innerPair864RoundedFacts :
    InnerPairRoundedFacts innerPair864Data innerPair864Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair864Input_eq }

noncomputable def innerPair865Data : WideLogData :=
  { lower := endpoint576
    upper := endpoint577 }

noncomputable def innerPair865Input : RationalEnclosure :=
  { lower := (2823707/2097152), upper := (2882549/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair865Input_eq :
    innerPair865Input = outerEnclosure 24 innerPair865Data.output := by
  rfl'

theorem innerPair865RoundedFacts :
    InnerPairRoundedFacts innerPair865Data innerPair865Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair865Input_eq }

noncomputable def innerPair866Data : WideLogData :=
  { lower := endpoint578
    upper := endpoint562 }

noncomputable def innerPair866Input : RationalEnclosure :=
  { lower := (5159785/4194304), upper := (2682669/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair866Input_eq :
    innerPair866Input = outerEnclosure 24 innerPair866Data.output := by
  rfl'

theorem innerPair866RoundedFacts :
    InnerPairRoundedFacts innerPair866Data innerPair866Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair866Input_eq }

noncomputable def innerPair867Data : WideLogData :=
  { lower := endpoint579
    upper := endpoint580 }

noncomputable def innerPair867Input : RationalEnclosure :=
  { lower := (21194821/16777216), upper := (21902291/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair867Input_eq :
    innerPair867Input = outerEnclosure 24 innerPair867Data.output := by
  rfl'

theorem innerPair867RoundedFacts :
    InnerPairRoundedFacts innerPair867Data innerPair867Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair867Input_eq }

noncomputable def innerPair868Data : WideLogData :=
  { lower := endpoint582
    upper := endpoint584 }

noncomputable def innerPair868Input : RationalEnclosure :=
  { lower := (5879569/4194304), upper := (24026717/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair868Input_eq :
    innerPair868Input = outerEnclosure 24 innerPair868Data.output := by
  rfl'

theorem innerPair868RoundedFacts :
    InnerPairRoundedFacts innerPair868Data innerPair868Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair868Input_eq }

noncomputable def innerPair869Data : WideLogData :=
  { lower := endpoint582
    upper := endpoint585 }

noncomputable def innerPair869Input : RationalEnclosure :=
  { lower := (5879569/4194304), upper := (24275273/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair869Input_eq :
    innerPair869Input = outerEnclosure 24 innerPair869Data.output := by
  rfl'

theorem innerPair869RoundedFacts :
    InnerPairRoundedFacts innerPair869Data innerPair869Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair869Input_eq }

noncomputable def innerPair870Data : WideLogData :=
  { lower := endpoint582
    upper := endpoint589 }

noncomputable def innerPair870Input : RationalEnclosure :=
  { lower := (5879569/4194304), upper := (24520201/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair870Input_eq :
    innerPair870Input = outerEnclosure 24 innerPair870Data.output := by
  rfl'

theorem innerPair870RoundedFacts :
    InnerPairRoundedFacts innerPair870Data innerPair870Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair870Input_eq }

noncomputable def innerPair871Data : WideLogData :=
  { lower := endpoint583
    upper := endpoint585 }

noncomputable def innerPair871Input : RationalEnclosure :=
  { lower := (11887211/8388608), upper := (24275273/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair871Input_eq :
    innerPair871Input = outerEnclosure 24 innerPair871Data.output := by
  rfl'

theorem innerPair871RoundedFacts :
    InnerPairRoundedFacts innerPair871Data innerPair871Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair871Input_eq }

noncomputable def innerPair872Data : WideLogData :=
  { lower := endpoint583
    upper := endpoint589 }

noncomputable def innerPair872Input : RationalEnclosure :=
  { lower := (11887211/8388608), upper := (24520201/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair872Input_eq :
    innerPair872Input = outerEnclosure 24 innerPair872Data.output := by
  rfl'

theorem innerPair872RoundedFacts :
    InnerPairRoundedFacts innerPair872Data innerPair872Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair872Input_eq }

noncomputable def innerPair873Data : WideLogData :=
  { lower := endpoint583
    upper := endpoint590 }

noncomputable def innerPair873Input : RationalEnclosure :=
  { lower := (11887211/8388608), upper := (6190401/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair873Input_eq :
    innerPair873Input = outerEnclosure 24 innerPair873Data.output := by
  rfl'

theorem innerPair873RoundedFacts :
    InnerPairRoundedFacts innerPair873Data innerPair873Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair873Input_eq }

noncomputable def innerPair874Data : WideLogData :=
  { lower := endpoint584
    upper := endpoint589 }

noncomputable def innerPair874Input : RationalEnclosure :=
  { lower := (6006679/4194304), upper := (24520201/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair874Input_eq :
    innerPair874Input = outerEnclosure 24 innerPair874Data.output := by
  rfl'

theorem innerPair874RoundedFacts :
    InnerPairRoundedFacts innerPair874Data innerPair874Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair874Input_eq }

noncomputable def innerPair875Data : WideLogData :=
  { lower := endpoint584
    upper := endpoint590 }

noncomputable def innerPair875Input : RationalEnclosure :=
  { lower := (6006679/4194304), upper := (6190401/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair875Input_eq :
    innerPair875Input = outerEnclosure 24 innerPair875Data.output := by
  rfl'

theorem innerPair875RoundedFacts :
    InnerPairRoundedFacts innerPair875Data innerPair875Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair875Input_eq }

noncomputable def innerPair876Data : WideLogData :=
  { lower := endpoint584
    upper := endpoint591 }

noncomputable def innerPair876Input : RationalEnclosure :=
  { lower := (6006679/4194304), upper := (12499791/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair876Input_eq :
    innerPair876Input = outerEnclosure 24 innerPair876Data.output := by
  rfl'

theorem innerPair876RoundedFacts :
    InnerPairRoundedFacts innerPair876Data innerPair876Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair876Input_eq }

noncomputable def innerPair877Data : WideLogData :=
  { lower := endpoint585
    upper := endpoint590 }

noncomputable def innerPair877Input : RationalEnclosure :=
  { lower := (3034409/2097152), upper := (6190401/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair877Input_eq :
    innerPair877Input = outerEnclosure 24 innerPair877Data.output := by
  rfl'

theorem innerPair877RoundedFacts :
    InnerPairRoundedFacts innerPair877Data innerPair877Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair877Input_eq }

noncomputable def innerPair878Data : WideLogData :=
  { lower := endpoint585
    upper := endpoint591 }

noncomputable def innerPair878Input : RationalEnclosure :=
  { lower := (3034409/2097152), upper := (12499791/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair878Input_eq :
    innerPair878Input = outerEnclosure 24 innerPair878Data.output := by
  rfl'

theorem innerPair878RoundedFacts :
    InnerPairRoundedFacts innerPair878Data innerPair878Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair878Input_eq }

noncomputable def innerPair879Data : WideLogData :=
  { lower := endpoint585
    upper := endpoint592 }

noncomputable def innerPair879Input : RationalEnclosure :=
  { lower := (3034409/2097152), upper := (3154279/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair879Input_eq :
    innerPair879Input = outerEnclosure 24 innerPair879Data.output := by
  rfl'

theorem innerPair879RoundedFacts :
    InnerPairRoundedFacts innerPair879Data innerPair879Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair879Input_eq }

noncomputable def innerPair880Data : WideLogData :=
  { lower := endpoint586
    upper := endpoint587 }

noncomputable def innerPair880Input : RationalEnclosure :=
  { lower := (22521317/16777216), upper := (23323569/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair880Input_eq :
    innerPair880Input = outerEnclosure 24 innerPair880Data.output := by
  rfl'

theorem innerPair880RoundedFacts :
    InnerPairRoundedFacts innerPair880Data innerPair880Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair880Input_eq }

noncomputable def innerPair881Data : WideLogData :=
  { lower := endpoint589
    upper := endpoint591 }

noncomputable def innerPair881Input : RationalEnclosure :=
  { lower := (24520199/16777216), upper := (12499791/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair881Input_eq :
    innerPair881Input = outerEnclosure 24 innerPair881Data.output := by
  rfl'

theorem innerPair881RoundedFacts :
    InnerPairRoundedFacts innerPair881Data innerPair881Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair881Input_eq }

noncomputable def innerPair882Data : WideLogData :=
  { lower := endpoint589
    upper := endpoint592 }

noncomputable def innerPair882Input : RationalEnclosure :=
  { lower := (24520199/16777216), upper := (3154279/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair882Input_eq :
    innerPair882Input = outerEnclosure 24 innerPair882Data.output := by
  rfl'

theorem innerPair882RoundedFacts :
    InnerPairRoundedFacts innerPair882Data innerPair882Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair882Input_eq }

noncomputable def innerPair883Data : WideLogData :=
  { lower := endpoint590
    upper := endpoint592 }

noncomputable def innerPair883Input : RationalEnclosure :=
  { lower := (12380801/8388608), upper := (3154279/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair883Input_eq :
    innerPair883Input = outerEnclosure 24 innerPair883Data.output := by
  rfl'

theorem innerPair883RoundedFacts :
    InnerPairRoundedFacts innerPair883Data innerPair883Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair883Input_eq }

noncomputable def innerPair884Data : WideLogData :=
  { lower := endpoint590
    upper := endpoint598 }

noncomputable def innerPair884Input : RationalEnclosure :=
  { lower := (12380801/8388608), upper := (12732823/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair884Input_eq :
    innerPair884Input = outerEnclosure 24 innerPair884Data.output := by
  rfl'

theorem innerPair884RoundedFacts :
    InnerPairRoundedFacts innerPair884Data innerPair884Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair884Input_eq }

noncomputable def innerPair885Data : WideLogData :=
  { lower := endpoint591
    upper := endpoint598 }

noncomputable def innerPair885Input : RationalEnclosure :=
  { lower := (24999581/16777216), upper := (12732823/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair885Input_eq :
    innerPair885Input = outerEnclosure 24 innerPair885Data.output := by
  rfl'

theorem innerPair885RoundedFacts :
    InnerPairRoundedFacts innerPair885Data innerPair885Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair885Input_eq }

noncomputable def innerPair886Data : WideLogData :=
  { lower := endpoint591
    upper := endpoint601 }

noncomputable def innerPair886Input : RationalEnclosure :=
  { lower := (24999581/16777216), upper := (25693911/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair886Input_eq :
    innerPair886Input = outerEnclosure 24 innerPair886Data.output := by
  rfl'

theorem innerPair886RoundedFacts :
    InnerPairRoundedFacts innerPair886Data innerPair886Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair886Input_eq }

noncomputable def innerPair887Data : WideLogData :=
  { lower := endpoint592
    upper := endpoint601 }

noncomputable def innerPair887Input : RationalEnclosure :=
  { lower := (25234231/16777216), upper := (25693911/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair887Input_eq :
    innerPair887Input = outerEnclosure 24 innerPair887Data.output := by
  rfl'

theorem innerPair887RoundedFacts :
    InnerPairRoundedFacts innerPair887Data innerPair887Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair887Input_eq }

noncomputable def innerPair888Data : WideLogData :=
  { lower := endpoint592
    upper := endpoint602 }

noncomputable def innerPair888Input : RationalEnclosure :=
  { lower := (25234231/16777216), upper := (3239889/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair888Input_eq :
    innerPair888Input = outerEnclosure 24 innerPair888Data.output := by
  rfl'

theorem innerPair888RoundedFacts :
    InnerPairRoundedFacts innerPair888Data innerPair888Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair888Input_eq }

noncomputable def innerPair889Data : WideLogData :=
  { lower := endpoint593
    upper := endpoint587 }

noncomputable def innerPair889Input : RationalEnclosure :=
  { lower := (22793019/16777216), upper := (23323569/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair889Input_eq :
    innerPair889Input = outerEnclosure 24 innerPair889Data.output := by
  rfl'

theorem innerPair889RoundedFacts :
    InnerPairRoundedFacts innerPair889Data innerPair889Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair889Input_eq }

noncomputable def innerPair890Data : WideLogData :=
  { lower := endpoint594
    upper := endpoint595 }

noncomputable def innerPair890Input : RationalEnclosure :=
  { lower := (23901043/16777216), upper := (3080167/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair890Input_eq :
    innerPair890Input = outerEnclosure 24 innerPair890Data.output := by
  rfl'

theorem innerPair890RoundedFacts :
    InnerPairRoundedFacts innerPair890Data innerPair890Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair890Input_eq }

noncomputable def innerPair891Data : WideLogData :=
  { lower := endpoint596
    upper := endpoint597 }

noncomputable def innerPair891Input : RationalEnclosure :=
  { lower := (12075727/8388608), upper := (24881015/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair891Input_eq :
    innerPair891Input = outerEnclosure 24 innerPair891Data.output := by
  rfl'

theorem innerPair891RoundedFacts :
    InnerPairRoundedFacts innerPair891Data innerPair891Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair891Input_eq }

noncomputable def innerPair892Data : WideLogData :=
  { lower := endpoint598
    upper := endpoint602 }

noncomputable def innerPair892Input : RationalEnclosure :=
  { lower := (6366411/4194304), upper := (3239889/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair892Input_eq :
    innerPair892Input = outerEnclosure 24 innerPair892Data.output := by
  rfl'

theorem innerPair892RoundedFacts :
    InnerPairRoundedFacts innerPair892Data innerPair892Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair892Input_eq }

noncomputable def innerPair893Data : WideLogData :=
  { lower := endpoint598
    upper := endpoint603 }

noncomputable def innerPair893Input : RationalEnclosure :=
  { lower := (6366411/4194304), upper := (13070665/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair893Input_eq :
    innerPair893Input = outerEnclosure 24 innerPair893Data.output := by
  rfl'

theorem innerPair893RoundedFacts :
    InnerPairRoundedFacts innerPair893Data innerPair893Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair893Input_eq }

noncomputable def innerPair894Data : WideLogData :=
  { lower := endpoint599
    upper := endpoint600 }

noncomputable def innerPair894Input : RationalEnclosure :=
  { lower := (6145219/4194304), upper := (12646193/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair894Input_eq :
    innerPair894Input = outerEnclosure 24 innerPair894Data.output := by
  rfl'

theorem innerPair894RoundedFacts :
    InnerPairRoundedFacts innerPair894Data innerPair894Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair894Input_eq }

noncomputable def innerPair895Data : WideLogData :=
  { lower := endpoint601
    upper := endpoint603 }

noncomputable def innerPair895Input : RationalEnclosure :=
  { lower := (25693909/16777216), upper := (13070665/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair895Input_eq :
    innerPair895Input = outerEnclosure 24 innerPair895Data.output := by
  rfl'

theorem innerPair895RoundedFacts :
    InnerPairRoundedFacts innerPair895Data innerPair895Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair895Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
