import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6

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

noncomputable def innerPair256Data : WideLogData :=
  { lower := endpoint74
    upper := endpoint75 }

noncomputable def innerPair256Input : RationalEnclosure :=
  { lower := (6566261/8388608), upper := (425161/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair256Input_eq :
    innerPair256Input = outerEnclosure 24 innerPair256Data.output := by
  rfl'

theorem innerPair256RoundedFacts :
    InnerPairRoundedFacts innerPair256Data innerPair256Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair256Input_eq }

noncomputable def innerPair257Data : WideLogData :=
  { lower := endpoint74
    upper := endpoint76 }

noncomputable def innerPair257Input : RationalEnclosure :=
  { lower := (6566261/8388608), upper := (14064831/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair257Input_eq :
    innerPair257Input = outerEnclosure 24 innerPair257Data.output := by
  rfl'

theorem innerPair257RoundedFacts :
    InnerPairRoundedFacts innerPair257Data innerPair257Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair257Input_eq }

noncomputable def innerPair258Data : WideLogData :=
  { lower := endpoint74
    upper := endpoint77 }

noncomputable def innerPair258Input : RationalEnclosure :=
  { lower := (6566261/8388608), upper := (7256125/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair258Input_eq :
    innerPair258Input = outerEnclosure 24 innerPair258Data.output := by
  rfl'

theorem innerPair258RoundedFacts :
    InnerPairRoundedFacts innerPair258Data innerPair258Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair258Input_eq }

noncomputable def innerPair259Data : WideLogData :=
  { lower := endpoint74
    upper := endpoint80 }

noncomputable def innerPair259Input : RationalEnclosure :=
  { lower := (6566261/8388608), upper := (6685251/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair259Input_eq :
    innerPair259Input = outerEnclosure 24 innerPair259Data.output := by
  rfl'

theorem innerPair259RoundedFacts :
    InnerPairRoundedFacts innerPair259Data innerPair259Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair259Input_eq }

noncomputable def innerPair260Data : WideLogData :=
  { lower := endpoint74
    upper := endpoint290 }

noncomputable def innerPair260Input : RationalEnclosure :=
  { lower := (6566261/8388608), upper := (13546797/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair260Input_eq :
    innerPair260Input = outerEnclosure 24 innerPair260Data.output := by
  rfl'

theorem innerPair260RoundedFacts :
    InnerPairRoundedFacts innerPair260Data innerPair260Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair260Input_eq }

noncomputable def innerPair261Data : WideLogData :=
  { lower := endpoint74
    upper := endpoint292 }

noncomputable def innerPair261Input : RationalEnclosure :=
  { lower := (6566261/8388608), upper := (6860629/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair261Input_eq :
    innerPair261Input = outerEnclosure 24 innerPair261Data.output := by
  rfl'

theorem innerPair261RoundedFacts :
    InnerPairRoundedFacts innerPair261Data innerPair261Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair261Input_eq }

noncomputable def innerPair262Data : WideLogData :=
  { lower := endpoint74
    upper := endpoint347 }

noncomputable def innerPair262Input : RationalEnclosure :=
  { lower := (6566261/8388608), upper := (13488237/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair262Input_eq :
    innerPair262Input = outerEnclosure 24 innerPair262Data.output := by
  rfl'

theorem innerPair262RoundedFacts :
    InnerPairRoundedFacts innerPair262Data innerPair262Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair262Input_eq }

noncomputable def innerPair263Data : WideLogData :=
  { lower := endpoint74
    upper := endpoint348 }

noncomputable def innerPair263Input : RationalEnclosure :=
  { lower := (6566261/8388608), upper := (13458881/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair263Input_eq :
    innerPair263Input = outerEnclosure 24 innerPair263Data.output := by
  rfl'

theorem innerPair263RoundedFacts :
    InnerPairRoundedFacts innerPair263Data innerPair263Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair263Input_eq }

noncomputable def innerPair264Data : WideLogData :=
  { lower := endpoint75
    upper := endpoint76 }

noncomputable def innerPair264Input : RationalEnclosure :=
  { lower := (13605151/16777216), upper := (14064831/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair264Input_eq :
    innerPair264Input = outerEnclosure 24 innerPair264Data.output := by
  rfl'

theorem innerPair264RoundedFacts :
    InnerPairRoundedFacts innerPair264Data innerPair264Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair264Input_eq }

noncomputable def innerPair265Data : WideLogData :=
  { lower := endpoint75
    upper := endpoint77 }

noncomputable def innerPair265Input : RationalEnclosure :=
  { lower := (13605151/16777216), upper := (7256125/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair265Input_eq :
    innerPair265Input = outerEnclosure 24 innerPair265Data.output := by
  rfl'

theorem innerPair265RoundedFacts :
    InnerPairRoundedFacts innerPair265Data innerPair265Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair265Input_eq }

noncomputable def innerPair266Data : WideLogData :=
  { lower := endpoint75
    upper := endpoint78 }

noncomputable def innerPair266Input : RationalEnclosure :=
  { lower := (13605151/16777216), upper := (7474023/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair266Input_eq :
    innerPair266Input = outerEnclosure 24 innerPair266Data.output := by
  rfl'

theorem innerPair266RoundedFacts :
    InnerPairRoundedFacts innerPair266Data innerPair266Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair266Input_eq }

noncomputable def innerPair267Data : WideLogData :=
  { lower := endpoint75
    upper := endpoint79 }

noncomputable def innerPair267Input : RationalEnclosure :=
  { lower := (13605151/16777216), upper := (1921601/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair267Input_eq :
    innerPair267Input = outerEnclosure 24 innerPair267Data.output := by
  rfl'

theorem innerPair267RoundedFacts :
    InnerPairRoundedFacts innerPair267Data innerPair267Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair267Input_eq }

noncomputable def innerPair268Data : WideLogData :=
  { lower := endpoint75
    upper := endpoint294 }

noncomputable def innerPair268Input : RationalEnclosure :=
  { lower := (13605151/16777216), upper := (3473481/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair268Input_eq :
    innerPair268Input = outerEnclosure 24 innerPair268Data.output := by
  rfl'

theorem innerPair268RoundedFacts :
    InnerPairRoundedFacts innerPair268Data innerPair268Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair268Input_eq }

noncomputable def innerPair269Data : WideLogData :=
  { lower := endpoint75
    upper := endpoint295 }

noncomputable def innerPair269Input : RationalEnclosure :=
  { lower := (13605151/16777216), upper := (6918283/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair269Input_eq :
    innerPair269Input = outerEnclosure 24 innerPair269Data.output := by
  rfl'

theorem innerPair269RoundedFacts :
    InnerPairRoundedFacts innerPair269Data innerPair269Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair269Input_eq }

noncomputable def innerPair270Data : WideLogData :=
  { lower := endpoint75
    upper := endpoint297 }

noncomputable def innerPair270Input : RationalEnclosure :=
  { lower := (13605151/16777216), upper := (893127/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair270Input_eq :
    innerPair270Input = outerEnclosure 24 innerPair270Data.output := by
  rfl'

theorem innerPair270RoundedFacts :
    InnerPairRoundedFacts innerPair270Data innerPair270Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair270Input_eq }

noncomputable def innerPair271Data : WideLogData :=
  { lower := endpoint75
    upper := endpoint298 }

noncomputable def innerPair271Input : RationalEnclosure :=
  { lower := (13605151/16777216), upper := (6975543/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair271Input_eq :
    innerPair271Input = outerEnclosure 24 innerPair271Data.output := by
  rfl'

theorem innerPair271RoundedFacts :
    InnerPairRoundedFacts innerPair271Data innerPair271Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair271Input_eq }

noncomputable def innerPair272Data : WideLogData :=
  { lower := endpoint76
    upper := endpoint77 }

noncomputable def innerPair272Input : RationalEnclosure :=
  { lower := (14064829/16777216), upper := (7256125/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair272Input_eq :
    innerPair272Input = outerEnclosure 24 innerPair272Data.output := by
  rfl'

theorem innerPair272RoundedFacts :
    InnerPairRoundedFacts innerPair272Data innerPair272Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair272Input_eq }

noncomputable def innerPair273Data : WideLogData :=
  { lower := endpoint76
    upper := endpoint78 }

noncomputable def innerPair273Input : RationalEnclosure :=
  { lower := (14064829/16777216), upper := (7474023/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair273Input_eq :
    innerPair273Input = outerEnclosure 24 innerPair273Data.output := by
  rfl'

theorem innerPair273RoundedFacts :
    InnerPairRoundedFacts innerPair273Data innerPair273Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair273Input_eq }

noncomputable def innerPair274Data : WideLogData :=
  { lower := endpoint76
    upper := endpoint79 }

noncomputable def innerPair274Input : RationalEnclosure :=
  { lower := (14064829/16777216), upper := (1921601/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair274Input_eq :
    innerPair274Input = outerEnclosure 24 innerPair274Data.output := by
  rfl'

theorem innerPair274RoundedFacts :
    InnerPairRoundedFacts innerPair274Data innerPair274Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair274Input_eq }

noncomputable def innerPair275Data : WideLogData :=
  { lower := endpoint76
    upper := endpoint90 }

noncomputable def innerPair275Input : RationalEnclosure :=
  { lower := (14064829/16777216), upper := (7893541/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair275Input_eq :
    innerPair275Input = outerEnclosure 24 innerPair275Data.output := by
  rfl'

theorem innerPair275RoundedFacts :
    InnerPairRoundedFacts innerPair275Data innerPair275Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair275Input_eq }

noncomputable def innerPair276Data : WideLogData :=
  { lower := endpoint76
    upper := endpoint297 }

noncomputable def innerPair276Input : RationalEnclosure :=
  { lower := (14064829/16777216), upper := (893127/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair276Input_eq :
    innerPair276Input = outerEnclosure 24 innerPair276Data.output := by
  rfl'

theorem innerPair276RoundedFacts :
    InnerPairRoundedFacts innerPair276Data innerPair276Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair276Input_eq }

noncomputable def innerPair277Data : WideLogData :=
  { lower := endpoint76
    upper := endpoint299 }

noncomputable def innerPair277Input : RationalEnclosure :=
  { lower := (14064829/16777216), upper := (14401509/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair277Input_eq :
    innerPair277Input = outerEnclosure 24 innerPair277Data.output := by
  rfl'

theorem innerPair277RoundedFacts :
    InnerPairRoundedFacts innerPair277Data innerPair277Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair277Input_eq }

noncomputable def innerPair278Data : WideLogData :=
  { lower := endpoint77
    upper := endpoint78 }

noncomputable def innerPair278Input : RationalEnclosure :=
  { lower := (1814031/2097152), upper := (7474023/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair278Input_eq :
    innerPair278Input = outerEnclosure 24 innerPair278Data.output := by
  rfl'

theorem innerPair278RoundedFacts :
    InnerPairRoundedFacts innerPair278Data innerPair278Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair278Input_eq }

noncomputable def innerPair279Data : WideLogData :=
  { lower := endpoint77
    upper := endpoint79 }

noncomputable def innerPair279Input : RationalEnclosure :=
  { lower := (1814031/2097152), upper := (1921601/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair279Input_eq :
    innerPair279Input = outerEnclosure 24 innerPair279Data.output := by
  rfl'

theorem innerPair279RoundedFacts :
    InnerPairRoundedFacts innerPair279Data innerPair279Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair279Input_eq }

noncomputable def innerPair280Data : WideLogData :=
  { lower := endpoint77
    upper := endpoint90 }

noncomputable def innerPair280Input : RationalEnclosure :=
  { lower := (1814031/2097152), upper := (7893541/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair280Input_eq :
    innerPair280Input = outerEnclosure 24 innerPair280Data.output := by
  rfl'

theorem innerPair280RoundedFacts :
    InnerPairRoundedFacts innerPair280Data innerPair280Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair280Input_eq }

noncomputable def innerPair281Data : WideLogData :=
  { lower := endpoint77
    upper := endpoint91 }

noncomputable def innerPair281Input : RationalEnclosure :=
  { lower := (1814031/2097152), upper := (16191371/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair281Input_eq :
    innerPair281Input = outerEnclosure 24 innerPair281Data.output := by
  rfl'

theorem innerPair281RoundedFacts :
    InnerPairRoundedFacts innerPair281Data innerPair281Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair281Input_eq }

noncomputable def innerPair282Data : WideLogData :=
  { lower := endpoint77
    upper := endpoint305 }

noncomputable def innerPair282Input : RationalEnclosure :=
  { lower := (1814031/2097152), upper := (14731563/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair282Input_eq :
    innerPair282Input = outerEnclosure 24 innerPair282Data.output := by
  rfl'

theorem innerPair282RoundedFacts :
    InnerPairRoundedFacts innerPair282Data innerPair282Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair282Input_eq }

noncomputable def innerPair283Data : WideLogData :=
  { lower := endpoint77
    upper := endpoint308 }

noncomputable def innerPair283Input : RationalEnclosure :=
  { lower := (1814031/2097152), upper := (7420077/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair283Input_eq :
    innerPair283Input = outerEnclosure 24 innerPair283Data.output := by
  rfl'

theorem innerPair283RoundedFacts :
    InnerPairRoundedFacts innerPair283Data innerPair283Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair283Input_eq }

noncomputable def innerPair284Data : WideLogData :=
  { lower := endpoint77
    upper := endpoint403 }

noncomputable def innerPair284Input : RationalEnclosure :=
  { lower := (1814031/2097152), upper := (15055249/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair284Input_eq :
    innerPair284Input = outerEnclosure 24 innerPair284Data.output := by
  rfl'

theorem innerPair284RoundedFacts :
    InnerPairRoundedFacts innerPair284Data innerPair284Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair284Input_eq }

noncomputable def innerPair285Data : WideLogData :=
  { lower := endpoint78
    upper := endpoint79 }

noncomputable def innerPair285Input : RationalEnclosure :=
  { lower := (14948045/16777216), upper := (1921601/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair285Input_eq :
    innerPair285Input = outerEnclosure 24 innerPair285Data.output := by
  rfl'

theorem innerPair285RoundedFacts :
    InnerPairRoundedFacts innerPair285Data innerPair285Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair285Input_eq }

noncomputable def innerPair286Data : WideLogData :=
  { lower := endpoint78
    upper := endpoint90 }

noncomputable def innerPair286Input : RationalEnclosure :=
  { lower := (14948045/16777216), upper := (7893541/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair286Input_eq :
    innerPair286Input = outerEnclosure 24 innerPair286Data.output := by
  rfl'

theorem innerPair286RoundedFacts :
    InnerPairRoundedFacts innerPair286Data innerPair286Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair286Input_eq }

noncomputable def innerPair287Data : WideLogData :=
  { lower := endpoint78
    upper := endpoint91 }

noncomputable def innerPair287Input : RationalEnclosure :=
  { lower := (14948045/16777216), upper := (16191371/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair287Input_eq :
    innerPair287Input = outerEnclosure 24 innerPair287Data.output := by
  rfl'

theorem innerPair287RoundedFacts :
    InnerPairRoundedFacts innerPair287Data innerPair287Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair287Input_eq }

noncomputable def innerPair288Data : WideLogData :=
  { lower := endpoint78
    upper := endpoint92 }

noncomputable def innerPair288Input : RationalEnclosure :=
  { lower := (14948045/16777216), upper := (4146537/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair288Input_eq :
    innerPair288Input = outerEnclosure 24 innerPair288Data.output := by
  rfl'

theorem innerPair288RoundedFacts :
    InnerPairRoundedFacts innerPair288Data innerPair288Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair288Input_eq }

noncomputable def innerPair289Data : WideLogData :=
  { lower := endpoint78
    upper := endpoint94 }

noncomputable def innerPair289Input : RationalEnclosure :=
  { lower := (14948045/16777216), upper := (15161771/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair289Input_eq :
    innerPair289Input = outerEnclosure 24 innerPair289Data.output := by
  rfl'

theorem innerPair289RoundedFacts :
    InnerPairRoundedFacts innerPair289Data innerPair289Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair289Input_eq }

noncomputable def innerPair290Data : WideLogData :=
  { lower := endpoint78
    upper := endpoint414 }

noncomputable def innerPair290Input : RationalEnclosure :=
  { lower := (14948045/16777216), upper := (7633811/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair290Input_eq :
    innerPair290Input = outerEnclosure 24 innerPair290Data.output := by
  rfl'

theorem innerPair290RoundedFacts :
    InnerPairRoundedFacts innerPair290Data innerPair290Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair290Input_eq }

noncomputable def innerPair291Data : WideLogData :=
  { lower := endpoint78
    upper := endpoint419 }

noncomputable def innerPair291Input : RationalEnclosure :=
  { lower := (14948045/16777216), upper := (3869335/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair291Input_eq :
    innerPair291Input = outerEnclosure 24 innerPair291Data.output := by
  rfl'

theorem innerPair291RoundedFacts :
    InnerPairRoundedFacts innerPair291Data innerPair291Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair291Input_eq }

noncomputable def innerPair292Data : WideLogData :=
  { lower := endpoint78
    upper := endpoint434 }

noncomputable def innerPair292Input : RationalEnclosure :=
  { lower := (14948045/16777216), upper := (1947653/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair292Input_eq :
    innerPair292Input = outerEnclosure 24 innerPair292Data.output := by
  rfl'

theorem innerPair292RoundedFacts :
    InnerPairRoundedFacts innerPair292Data innerPair292Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair292Input_eq }

noncomputable def innerPair293Data : WideLogData :=
  { lower := endpoint79
    upper := endpoint90 }

noncomputable def innerPair293Input : RationalEnclosure :=
  { lower := (15372807/16777216), upper := (7893541/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair293Input_eq :
    innerPair293Input = outerEnclosure 24 innerPair293Data.output := by
  rfl'

theorem innerPair293RoundedFacts :
    InnerPairRoundedFacts innerPair293Data innerPair293Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair293Input_eq }

noncomputable def innerPair294Data : WideLogData :=
  { lower := endpoint79
    upper := endpoint91 }

noncomputable def innerPair294Input : RationalEnclosure :=
  { lower := (15372807/16777216), upper := (16191371/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair294Input_eq :
    innerPair294Input = outerEnclosure 24 innerPair294Data.output := by
  rfl'

theorem innerPair294RoundedFacts :
    InnerPairRoundedFacts innerPair294Data innerPair294Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair294Input_eq }

noncomputable def innerPair295Data : WideLogData :=
  { lower := endpoint79
    upper := endpoint92 }

noncomputable def innerPair295Input : RationalEnclosure :=
  { lower := (15372807/16777216), upper := (4146537/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair295Input_eq :
    innerPair295Input = outerEnclosure 24 innerPair295Data.output := by
  rfl'

theorem innerPair295RoundedFacts :
    InnerPairRoundedFacts innerPair295Data innerPair295Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair295Input_eq }

noncomputable def innerPair296Data : WideLogData :=
  { lower := endpoint79
    upper := endpoint93 }

noncomputable def innerPair296Input : RationalEnclosure :=
  { lower := (15372807/16777216), upper := (2121481/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair296Input_eq :
    innerPair296Input = outerEnclosure 24 innerPair296Data.output := by
  rfl'

theorem innerPair296RoundedFacts :
    InnerPairRoundedFacts innerPair296Data innerPair296Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair296Input_eq }

noncomputable def innerPair297Data : WideLogData :=
  { lower := endpoint79
    upper := endpoint434 }

noncomputable def innerPair297Input : RationalEnclosure :=
  { lower := (15372807/16777216), upper := (1947653/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair297Input_eq :
    innerPair297Input = outerEnclosure 24 innerPair297Data.output := by
  rfl'

theorem innerPair297RoundedFacts :
    InnerPairRoundedFacts innerPair297Data innerPair297Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair297Input_eq }

noncomputable def innerPair298Data : WideLogData :=
  { lower := endpoint79
    upper := endpoint435 }

noncomputable def innerPair298Input : RationalEnclosure :=
  { lower := (15372807/16777216), upper := (15889071/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair298Input_eq :
    innerPair298Input = outerEnclosure 24 innerPair298Data.output := by
  rfl'

theorem innerPair298RoundedFacts :
    InnerPairRoundedFacts innerPair298Data innerPair298Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair298Input_eq }

noncomputable def innerPair299Data : WideLogData :=
  { lower := endpoint79
    upper := endpoint437 }

noncomputable def innerPair299Input : RationalEnclosure :=
  { lower := (15372807/16777216), upper := (3921117/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair299Input_eq :
    innerPair299Input = outerEnclosure 24 innerPair299Data.output := by
  rfl'

theorem innerPair299RoundedFacts :
    InnerPairRoundedFacts innerPair299Data innerPair299Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair299Input_eq }

noncomputable def innerPair300Data : WideLogData :=
  { lower := endpoint80
    upper := endpoint292 }

noncomputable def innerPair300Input : RationalEnclosure :=
  { lower := (13370501/16777216), upper := (6860629/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair300Input_eq :
    innerPair300Input = outerEnclosure 24 innerPair300Data.output := by
  rfl'

theorem innerPair300RoundedFacts :
    InnerPairRoundedFacts innerPair300Data innerPair300Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair300Input_eq }

noncomputable def innerPair301Data : WideLogData :=
  { lower := endpoint80
    upper := endpoint295 }

noncomputable def innerPair301Input : RationalEnclosure :=
  { lower := (13370501/16777216), upper := (6918283/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair301Input_eq :
    innerPair301Input = outerEnclosure 24 innerPair301Data.output := by
  rfl'

theorem innerPair301RoundedFacts :
    InnerPairRoundedFacts innerPair301Data innerPair301Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair301Input_eq }

noncomputable def innerPair302Data : WideLogData :=
  { lower := endpoint80
    upper := endpoint298 }

noncomputable def innerPair302Input : RationalEnclosure :=
  { lower := (13370501/16777216), upper := (6975543/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair302Input_eq :
    innerPair302Input = outerEnclosure 24 innerPair302Data.output := by
  rfl'

theorem innerPair302RoundedFacts :
    InnerPairRoundedFacts innerPair302Data innerPair302Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair302Input_eq }

noncomputable def innerPair303Data : WideLogData :=
  { lower := endpoint80
    upper := endpoint380 }

noncomputable def innerPair303Input : RationalEnclosure :=
  { lower := (13370501/16777216), upper := (212125/262144) }

set_option maxRecDepth 1000000 in
private theorem innerPair303Input_eq :
    innerPair303Input = outerEnclosure 24 innerPair303Data.output := by
  rfl'

theorem innerPair303RoundedFacts :
    InnerPairRoundedFacts innerPair303Data innerPair303Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair303Input_eq }

noncomputable def innerPair304Data : WideLogData :=
  { lower := endpoint81
    upper := endpoint71 }

noncomputable def innerPair304Input : RationalEnclosure :=
  { lower := (171259/262144), upper := (11231183/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair304Input_eq :
    innerPair304Input = outerEnclosure 24 innerPair304Data.output := by
  rfl'

theorem innerPair304RoundedFacts :
    InnerPairRoundedFacts innerPair304Data innerPair304Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair304Input_eq }

noncomputable def innerPair305Data : WideLogData :=
  { lower := endpoint81
    upper := endpoint82 }

noncomputable def innerPair305Input : RationalEnclosure :=
  { lower := (171259/262144), upper := (5944599/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair305Input_eq :
    innerPair305Input = outerEnclosure 24 innerPair305Data.output := by
  rfl'

theorem innerPair305RoundedFacts :
    InnerPairRoundedFacts innerPair305Data innerPair305Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair305Input_eq }

noncomputable def innerPair306Data : WideLogData :=
  { lower := endpoint81
    upper := endpoint85 }

noncomputable def innerPair306Input : RationalEnclosure :=
  { lower := (171259/262144), upper := (11364867/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair306Input_eq :
    innerPair306Input = outerEnclosure 24 innerPair306Data.output := by
  rfl'

theorem innerPair306RoundedFacts :
    InnerPairRoundedFacts innerPair306Data innerPair306Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair306Input_eq }

noncomputable def innerPair307Data : WideLogData :=
  { lower := endpoint81
    upper := endpoint266 }

noncomputable def innerPair307Input : RationalEnclosure :=
  { lower := (171259/262144), upper := (176011/262144) }

set_option maxRecDepth 1000000 in
private theorem innerPair307Input_eq :
    innerPair307Input = outerEnclosure 24 innerPair307Data.output := by
  rfl'

theorem innerPair307RoundedFacts :
    InnerPairRoundedFacts innerPair307Data innerPair307Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair307Input_eq }

noncomputable def innerPair308Data : WideLogData :=
  { lower := endpoint81
    upper := endpoint267 }

noncomputable def innerPair308Input : RationalEnclosure :=
  { lower := (171259/262144), upper := (5748747/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair308Input_eq :
    innerPair308Input = outerEnclosure 24 innerPair308Data.output := by
  rfl'

theorem innerPair308RoundedFacts :
    InnerPairRoundedFacts innerPair308Data innerPair308Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair308Input_eq }

noncomputable def innerPair309Data : WideLogData :=
  { lower := endpoint81
    upper := endpoint270 }

noncomputable def innerPair309Input : RationalEnclosure :=
  { lower := (171259/262144), upper := (5569327/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair309Input_eq :
    innerPair309Input = outerEnclosure 24 innerPair309Data.output := by
  rfl'

theorem innerPair309RoundedFacts :
    InnerPairRoundedFacts innerPair309Data innerPair309Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair309Input_eq }

noncomputable def innerPair310Data : WideLogData :=
  { lower := endpoint81
    upper := endpoint273 }

noncomputable def innerPair310Input : RationalEnclosure :=
  { lower := (171259/262144), upper := (2790985/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair310Input_eq :
    innerPair310Input = outerEnclosure 24 innerPair310Data.output := by
  rfl'

theorem innerPair310RoundedFacts :
    InnerPairRoundedFacts innerPair310Data innerPair310Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair310Input_eq }

noncomputable def innerPair311Data : WideLogData :=
  { lower := endpoint82
    upper := endpoint86 }

noncomputable def innerPair311Input : RationalEnclosure :=
  { lower := (11889197/16777216), upper := (12271965/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair311Input_eq :
    innerPair311Input = outerEnclosure 24 innerPair311Data.output := by
  rfl'

theorem innerPair311RoundedFacts :
    InnerPairRoundedFacts innerPair311Data innerPair311Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair311Input_eq }

noncomputable def innerPair312Data : WideLogData :=
  { lower := endpoint82
    upper := endpoint284 }

noncomputable def innerPair312Input : RationalEnclosure :=
  { lower := (11889197/16777216), upper := (12397637/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair312Input_eq :
    innerPair312Input = outerEnclosure 24 innerPair312Data.output := by
  rfl'

theorem innerPair312RoundedFacts :
    InnerPairRoundedFacts innerPair312Data innerPair312Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair312Input_eq }

noncomputable def innerPair313Data : WideLogData :=
  { lower := endpoint83
    upper := endpoint84 }

noncomputable def innerPair313Input : RationalEnclosure :=
  { lower := (11298157/16777216), upper := (12081673/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair313Input_eq :
    innerPair313Input = outerEnclosure 24 innerPair313Data.output := by
  rfl'

theorem innerPair313RoundedFacts :
    InnerPairRoundedFacts innerPair313Data innerPair313Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair313Input_eq }

noncomputable def innerPair314Data : WideLogData :=
  { lower := endpoint83
    upper := endpoint277 }

noncomputable def innerPair314Input : RationalEnclosure :=
  { lower := (11298157/16777216), upper := (1441311/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair314Input_eq :
    innerPair314Input = outerEnclosure 24 innerPair314Data.output := by
  rfl'

theorem innerPair314RoundedFacts :
    InnerPairRoundedFacts innerPair314Data innerPair314Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair314Input_eq }

noncomputable def innerPair315Data : WideLogData :=
  { lower := endpoint83
    upper := endpoint279 }

noncomputable def innerPair315Input : RationalEnclosure :=
  { lower := (11298157/16777216), upper := (5736353/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair315Input_eq :
    innerPair315Input = outerEnclosure 24 innerPair315Data.output := by
  rfl'

theorem innerPair315RoundedFacts :
    InnerPairRoundedFacts innerPair315Data innerPair315Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair315Input_eq }

noncomputable def innerPair316Data : WideLogData :=
  { lower := endpoint84
    upper := endpoint327 }

noncomputable def innerPair316Input : RationalEnclosure :=
  { lower := (12081671/16777216), upper := (12303471/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair316Input_eq :
    innerPair316Input = outerEnclosure 24 innerPair316Data.output := by
  rfl'

theorem innerPair316RoundedFacts :
    InnerPairRoundedFacts innerPair316Data innerPair316Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair316Input_eq }

noncomputable def innerPair317Data : WideLogData :=
  { lower := endpoint85
    upper := endpoint82 }

noncomputable def innerPair317Input : RationalEnclosure :=
  { lower := (5682433/8388608), upper := (5944599/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair317Input_eq :
    innerPair317Input = outerEnclosure 24 innerPair317Data.output := by
  rfl'

theorem innerPair317RoundedFacts :
    InnerPairRoundedFacts innerPair317Data innerPair317Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair317Input_eq }

noncomputable def innerPair318Data : WideLogData :=
  { lower := endpoint85
    upper := endpoint86 }

noncomputable def innerPair318Input : RationalEnclosure :=
  { lower := (5682433/8388608), upper := (12271965/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair318Input_eq :
    innerPair318Input = outerEnclosure 24 innerPair318Data.output := by
  rfl'

theorem innerPair318RoundedFacts :
    InnerPairRoundedFacts innerPair318Data innerPair318Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair318Input_eq }

noncomputable def innerPair319Data : WideLogData :=
  { lower := endpoint85
    upper := endpoint87 }

noncomputable def innerPair319Input : RationalEnclosure :=
  { lower := (5682433/8388608), upper := (375555/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair319Input_eq :
    innerPair319Input = outerEnclosure 24 innerPair319Data.output := by
  rfl'

theorem innerPair319RoundedFacts :
    InnerPairRoundedFacts innerPair319Data innerPair319Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair319Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
