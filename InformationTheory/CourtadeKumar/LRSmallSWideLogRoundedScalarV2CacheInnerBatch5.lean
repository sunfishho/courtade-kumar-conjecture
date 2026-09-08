import InformationTheory.CourtadeKumar.LRSmallSWideLogFactoredRoundedCore
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch1
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch4
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch5
import InformationTheory.CourtadeKumar.LRSmallSWideLogRoundedScalarV2CacheEndpointBatch6
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

noncomputable def innerPair320Data : WideLogData :=
  { lower := endpoint85
    upper := endpoint277 }

noncomputable def innerPair320Input : RationalEnclosure :=
  { lower := (5682433/8388608), upper := (1441311/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair320Input_eq :
    innerPair320Input = outerEnclosure 24 innerPair320Data.output := by
  rfl'

theorem innerPair320RoundedFacts :
    InnerPairRoundedFacts innerPair320Data innerPair320Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair320Input_eq }

noncomputable def innerPair321Data : WideLogData :=
  { lower := endpoint85
    upper := endpoint283 }

noncomputable def innerPair321Input : RationalEnclosure :=
  { lower := (5682433/8388608), upper := (11759643/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair321Input_eq :
    innerPair321Input = outerEnclosure 24 innerPair321Data.output := by
  rfl'

theorem innerPair321RoundedFacts :
    InnerPairRoundedFacts innerPair321Data innerPair321Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair321Input_eq }

noncomputable def innerPair322Data : WideLogData :=
  { lower := endpoint86
    upper := endpoint88 }

noncomputable def innerPair322Input : RationalEnclosure :=
  { lower := (12271963/16777216), upper := (805695/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair322Input_eq :
    innerPair322Input = outerEnclosure 24 innerPair322Data.output := by
  rfl'

theorem innerPair322RoundedFacts :
    InnerPairRoundedFacts innerPair322Data innerPair322Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair322Input_eq }

noncomputable def innerPair323Data : WideLogData :=
  { lower := endpoint86
    upper := endpoint89 }

noncomputable def innerPair323Input : RationalEnclosure :=
  { lower := (12271963/16777216), upper := (12522375/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair323Input_eq :
    innerPair323Input = outerEnclosure 24 innerPair323Data.output := by
  rfl'

theorem innerPair323RoundedFacts :
    InnerPairRoundedFacts innerPair323Data innerPair323Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair323Input_eq }

noncomputable def innerPair324Data : WideLogData :=
  { lower := endpoint86
    upper := endpoint289 }

noncomputable def innerPair324Input : RationalEnclosure :=
  { lower := (12271963/16777216), upper := (798069/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair324Input_eq :
    innerPair324Input = outerEnclosure 24 innerPair324Data.output := by
  rfl'

theorem innerPair324RoundedFacts :
    InnerPairRoundedFacts innerPair324Data innerPair324Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair324Input_eq }

noncomputable def innerPair325Data : WideLogData :=
  { lower := endpoint86
    upper := endpoint334 }

noncomputable def innerPair325Input : RationalEnclosure :=
  { lower := (12271963/16777216), upper := (12584399/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair325Input_eq :
    innerPair325Input = outerEnclosure 24 innerPair325Data.output := by
  rfl'

theorem innerPair325RoundedFacts :
    InnerPairRoundedFacts innerPair325Data innerPair325Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair325Input_eq }

noncomputable def innerPair326Data : WideLogData :=
  { lower := endpoint86
    upper := endpoint337 }

noncomputable def innerPair326Input : RationalEnclosure :=
  { lower := (12271963/16777216), upper := (406633/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair326Input_eq :
    innerPair326Input = outerEnclosure 24 innerPair326Data.output := by
  rfl'

theorem innerPair326RoundedFacts :
    InnerPairRoundedFacts innerPair326Data innerPair326Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair326Input_eq }

noncomputable def innerPair327Data : WideLogData :=
  { lower := endpoint87
    upper := endpoint86 }

noncomputable def innerPair327Input : RationalEnclosure :=
  { lower := (6008879/8388608), upper := (12271965/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair327Input_eq :
    innerPair327Input = outerEnclosure 24 innerPair327Data.output := by
  rfl'

theorem innerPair327RoundedFacts :
    InnerPairRoundedFacts innerPair327Data innerPair327Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair327Input_eq }

noncomputable def innerPair328Data : WideLogData :=
  { lower := endpoint87
    upper := endpoint88 }

noncomputable def innerPair328Input : RationalEnclosure :=
  { lower := (6008879/8388608), upper := (805695/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair328Input_eq :
    innerPair328Input = outerEnclosure 24 innerPair328Data.output := by
  rfl'

theorem innerPair328RoundedFacts :
    InnerPairRoundedFacts innerPair328Data innerPair328Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair328Input_eq }

noncomputable def innerPair329Data : WideLogData :=
  { lower := endpoint87
    upper := endpoint284 }

noncomputable def innerPair329Input : RationalEnclosure :=
  { lower := (6008879/8388608), upper := (12397637/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair329Input_eq :
    innerPair329Input = outerEnclosure 24 innerPair329Data.output := by
  rfl'

theorem innerPair329RoundedFacts :
    InnerPairRoundedFacts innerPair329Data innerPair329Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair329Input_eq }

noncomputable def innerPair330Data : WideLogData :=
  { lower := endpoint87
    upper := endpoint289 }

noncomputable def innerPair330Input : RationalEnclosure :=
  { lower := (6008879/8388608), upper := (798069/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair330Input_eq :
    innerPair330Input = outerEnclosure 24 innerPair330Data.output := by
  rfl'

theorem innerPair330RoundedFacts :
    InnerPairRoundedFacts innerPair330Data innerPair330Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair330Input_eq }

noncomputable def innerPair331Data : WideLogData :=
  { lower := endpoint88
    upper := endpoint80 }

noncomputable def innerPair331Input : RationalEnclosure :=
  { lower := (12891119/16777216), upper := (6685251/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair331Input_eq :
    innerPair331Input = outerEnclosure 24 innerPair331Data.output := by
  rfl'

theorem innerPair331RoundedFacts :
    InnerPairRoundedFacts innerPair331Data innerPair331Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair331Input_eq }

noncomputable def innerPair332Data : WideLogData :=
  { lower := endpoint88
    upper := endpoint291 }

noncomputable def innerPair332Input : RationalEnclosure :=
  { lower := (12891119/16777216), upper := (13251935/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair332Input_eq :
    innerPair332Input = outerEnclosure 24 innerPair332Data.output := by
  rfl'

theorem innerPair332RoundedFacts :
    InnerPairRoundedFacts innerPair332Data innerPair332Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair332Input_eq }

noncomputable def innerPair333Data : WideLogData :=
  { lower := endpoint88
    upper := endpoint370 }

noncomputable def innerPair333Input : RationalEnclosure :=
  { lower := (12891119/16777216), upper := (3271881/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair333Input_eq :
    innerPair333Input = outerEnclosure 24 innerPair333Data.output := by
  rfl'

theorem innerPair333RoundedFacts :
    InnerPairRoundedFacts innerPair333Data innerPair333Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair333Input_eq }

noncomputable def innerPair334Data : WideLogData :=
  { lower := endpoint89
    upper := endpoint80 }

noncomputable def innerPair334Input : RationalEnclosure :=
  { lower := (6261187/8388608), upper := (6685251/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair334Input_eq :
    innerPair334Input = outerEnclosure 24 innerPair334Data.output := by
  rfl'

theorem innerPair334RoundedFacts :
    InnerPairRoundedFacts innerPair334Data innerPair334Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair334Input_eq }

noncomputable def innerPair335Data : WideLogData :=
  { lower := endpoint89
    upper := endpoint88 }

noncomputable def innerPair335Input : RationalEnclosure :=
  { lower := (6261187/8388608), upper := (805695/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair335Input_eq :
    innerPair335Input = outerEnclosure 24 innerPair335Data.output := by
  rfl'

theorem innerPair335RoundedFacts :
    InnerPairRoundedFacts innerPair335Data innerPair335Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair335Input_eq }

noncomputable def innerPair336Data : WideLogData :=
  { lower := endpoint89
    upper := endpoint289 }

noncomputable def innerPair336Input : RationalEnclosure :=
  { lower := (6261187/8388608), upper := (798069/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair336Input_eq :
    innerPair336Input = outerEnclosure 24 innerPair336Data.output := by
  rfl'

theorem innerPair336RoundedFacts :
    InnerPairRoundedFacts innerPair336Data innerPair336Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair336Input_eq }

noncomputable def innerPair337Data : WideLogData :=
  { lower := endpoint89
    upper := endpoint291 }

noncomputable def innerPair337Input : RationalEnclosure :=
  { lower := (6261187/8388608), upper := (13251935/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair337Input_eq :
    innerPair337Input = outerEnclosure 24 innerPair337Data.output := by
  rfl'

theorem innerPair337RoundedFacts :
    InnerPairRoundedFacts innerPair337Data innerPair337Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair337Input_eq }

noncomputable def innerPair338Data : WideLogData :=
  { lower := endpoint89
    upper := endpoint337 }

noncomputable def innerPair338Input : RationalEnclosure :=
  { lower := (6261187/8388608), upper := (406633/524288) }

set_option maxRecDepth 1000000 in
private theorem innerPair338Input_eq :
    innerPair338Input = outerEnclosure 24 innerPair338Data.output := by
  rfl'

theorem innerPair338RoundedFacts :
    InnerPairRoundedFacts innerPair338Data innerPair338Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair338Input_eq }

noncomputable def innerPair339Data : WideLogData :=
  { lower := endpoint90
    upper := endpoint91 }

noncomputable def innerPair339Input : RationalEnclosure :=
  { lower := (1973385/2097152), upper := (16191371/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair339Input_eq :
    innerPair339Input = outerEnclosure 24 innerPair339Data.output := by
  rfl'

theorem innerPair339RoundedFacts :
    InnerPairRoundedFacts innerPair339Data innerPair339Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair339Input_eq }

noncomputable def innerPair340Data : WideLogData :=
  { lower := endpoint90
    upper := endpoint92 }

noncomputable def innerPair340Input : RationalEnclosure :=
  { lower := (1973385/2097152), upper := (4146537/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair340Input_eq :
    innerPair340Input = outerEnclosure 24 innerPair340Data.output := by
  rfl'

theorem innerPair340RoundedFacts :
    InnerPairRoundedFacts innerPair340Data innerPair340Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair340Input_eq }

noncomputable def innerPair341Data : WideLogData :=
  { lower := endpoint90
    upper := endpoint93 }

noncomputable def innerPair341Input : RationalEnclosure :=
  { lower := (1973385/2097152), upper := (2121481/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair341Input_eq :
    innerPair341Input = outerEnclosure 24 innerPair341Data.output := by
  rfl'

theorem innerPair341RoundedFacts :
    InnerPairRoundedFacts innerPair341Data innerPair341Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair341Input_eq }

noncomputable def innerPair342Data : WideLogData :=
  { lower := endpoint90
    upper := endpoint95 }

noncomputable def innerPair342Input : RationalEnclosure :=
  { lower := (1973385/2097152), upper := (4072735/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair342Input_eq :
    innerPair342Input = outerEnclosure 24 innerPair342Data.output := by
  rfl'

theorem innerPair342RoundedFacts :
    InnerPairRoundedFacts innerPair342Data innerPair342Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair342Input_eq }

noncomputable def innerPair343Data : WideLogData :=
  { lower := endpoint90
    upper := endpoint96 }

noncomputable def innerPair343Input : RationalEnclosure :=
  { lower := (1973385/2097152), upper := (1084305/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair343Input_eq :
    innerPair343Input = outerEnclosure 24 innerPair343Data.output := by
  rfl'

theorem innerPair343RoundedFacts :
    InnerPairRoundedFacts innerPair343Data innerPair343Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair343Input_eq }

noncomputable def innerPair344Data : WideLogData :=
  { lower := endpoint90
    upper := endpoint444 }

noncomputable def innerPair344Input : RationalEnclosure :=
  { lower := (1973385/2097152), upper := (16091209/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair344Input_eq :
    innerPair344Input = outerEnclosure 24 innerPair344Data.output := by
  rfl'

theorem innerPair344RoundedFacts :
    InnerPairRoundedFacts innerPair344Data innerPair344Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair344Input_eq }

noncomputable def innerPair345Data : WideLogData :=
  { lower := endpoint91
    upper := endpoint92 }

noncomputable def innerPair345Input : RationalEnclosure :=
  { lower := (8095685/8388608), upper := (4146537/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair345Input_eq :
    innerPair345Input = outerEnclosure 24 innerPair345Data.output := by
  rfl'

theorem innerPair345RoundedFacts :
    InnerPairRoundedFacts innerPair345Data innerPair345Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair345Input_eq }

noncomputable def innerPair346Data : WideLogData :=
  { lower := endpoint91
    upper := endpoint93 }

noncomputable def innerPair346Input : RationalEnclosure :=
  { lower := (8095685/8388608), upper := (2121481/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair346Input_eq :
    innerPair346Input = outerEnclosure 24 innerPair346Data.output := by
  rfl'

theorem innerPair346RoundedFacts :
    InnerPairRoundedFacts innerPair346Data innerPair346Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair346Input_eq }

noncomputable def innerPair347Data : WideLogData :=
  { lower := endpoint91
    upper := endpoint96 }

noncomputable def innerPair347Input : RationalEnclosure :=
  { lower := (8095685/8388608), upper := (1084305/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair347Input_eq :
    innerPair347Input = outerEnclosure 24 innerPair347Data.output := by
  rfl'

theorem innerPair347RoundedFacts :
    InnerPairRoundedFacts innerPair347Data innerPair347Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair347Input_eq }

noncomputable def innerPair348Data : WideLogData :=
  { lower := endpoint91
    upper := endpoint451 }

noncomputable def innerPair348Input : RationalEnclosure :=
  { lower := (8095685/8388608), upper := (16683407/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair348Input_eq :
    innerPair348Input = outerEnclosure 24 innerPair348Data.output := by
  rfl'

theorem innerPair348RoundedFacts :
    InnerPairRoundedFacts innerPair348Data innerPair348Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair348Input_eq }

noncomputable def innerPair349Data : WideLogData :=
  { lower := endpoint91
    upper := endpoint460 }

noncomputable def innerPair349Input : RationalEnclosure :=
  { lower := (8095685/8388608), upper := (17066903/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair349Input_eq :
    innerPair349Input = outerEnclosure 24 innerPair349Data.output := by
  rfl'

theorem innerPair349RoundedFacts :
    InnerPairRoundedFacts innerPair349Data innerPair349Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair349Input_eq }

noncomputable def innerPair350Data : WideLogData :=
  { lower := endpoint91
    upper := endpoint461 }

noncomputable def innerPair350Input : RationalEnclosure :=
  { lower := (8095685/8388608), upper := (8390053/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair350Input_eq :
    innerPair350Input = outerEnclosure 24 innerPair350Data.output := by
  rfl'

theorem innerPair350RoundedFacts :
    InnerPairRoundedFacts innerPair350Data innerPair350Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair350Input_eq }

noncomputable def innerPair351Data : WideLogData :=
  { lower := endpoint91
    upper := endpoint465 }

noncomputable def innerPair351Input : RationalEnclosure :=
  { lower := (8095685/8388608), upper := (8353817/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair351Input_eq :
    innerPair351Input = outerEnclosure 24 innerPair351Data.output := by
  rfl'

theorem innerPair351RoundedFacts :
    InnerPairRoundedFacts innerPair351Data innerPair351Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair351Input_eq }

noncomputable def innerPair352Data : WideLogData :=
  { lower := endpoint92
    upper := endpoint93 }

noncomputable def innerPair352Input : RationalEnclosure :=
  { lower := (8293073/8388608), upper := (2121481/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair352Input_eq :
    innerPair352Input = outerEnclosure 24 innerPair352Data.output := by
  rfl'

theorem innerPair352RoundedFacts :
    InnerPairRoundedFacts innerPair352Data innerPair352Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair352Input_eq }

noncomputable def innerPair353Data : WideLogData :=
  { lower := endpoint92
    upper := endpoint96 }

noncomputable def innerPair353Input : RationalEnclosure :=
  { lower := (8293073/8388608), upper := (1084305/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair353Input_eq :
    innerPair353Input = outerEnclosure 24 innerPair353Data.output := by
  rfl'

theorem innerPair353RoundedFacts :
    InnerPairRoundedFacts innerPair353Data innerPair353Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair353Input_eq }

noncomputable def innerPair354Data : WideLogData :=
  { lower := endpoint92
    upper := endpoint97 }

noncomputable def innerPair354Input : RationalEnclosure :=
  { lower := (8293073/8388608), upper := (17717625/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair354Input_eq :
    innerPair354Input = outerEnclosure 24 innerPair354Data.output := by
  rfl'

theorem innerPair354RoundedFacts :
    InnerPairRoundedFacts innerPair354Data innerPair354Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair354Input_eq }

noncomputable def innerPair355Data : WideLogData :=
  { lower := endpoint92
    upper := endpoint460 }

noncomputable def innerPair355Input : RationalEnclosure :=
  { lower := (8293073/8388608), upper := (17066903/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair355Input_eq :
    innerPair355Input = outerEnclosure 24 innerPair355Data.output := by
  rfl'

theorem innerPair355RoundedFacts :
    InnerPairRoundedFacts innerPair355Data innerPair355Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair355Input_eq }

noncomputable def innerPair356Data : WideLogData :=
  { lower := endpoint93
    upper := endpoint96 }

noncomputable def innerPair356Input : RationalEnclosure :=
  { lower := (8485923/8388608), upper := (1084305/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair356Input_eq :
    innerPair356Input = outerEnclosure 24 innerPair356Data.output := by
  rfl'

theorem innerPair356RoundedFacts :
    InnerPairRoundedFacts innerPair356Data innerPair356Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair356Input_eq }

noncomputable def innerPair357Data : WideLogData :=
  { lower := endpoint93
    upper := endpoint97 }

noncomputable def innerPair357Input : RationalEnclosure :=
  { lower := (8485923/8388608), upper := (17717625/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair357Input_eq :
    innerPair357Input = outerEnclosure 24 innerPair357Data.output := by
  rfl'

theorem innerPair357RoundedFacts :
    InnerPairRoundedFacts innerPair357Data innerPair357Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair357Input_eq }

noncomputable def innerPair358Data : WideLogData :=
  { lower := endpoint93
    upper := endpoint98 }

noncomputable def innerPair358Input : RationalEnclosure :=
  { lower := (8485923/8388608), upper := (18078439/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair358Input_eq :
    innerPair358Input = outerEnclosure 24 innerPair358Data.output := by
  rfl'

theorem innerPair358RoundedFacts :
    InnerPairRoundedFacts innerPair358Data innerPair358Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair358Input_eq }

noncomputable def innerPair359Data : WideLogData :=
  { lower := endpoint93
    upper := endpoint464 }

noncomputable def innerPair359Input : RationalEnclosure :=
  { lower := (8485923/8388608), upper := (17441829/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair359Input_eq :
    innerPair359Input = outerEnclosure 24 innerPair359Data.output := by
  rfl'

theorem innerPair359RoundedFacts :
    InnerPairRoundedFacts innerPair359Data innerPair359Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair359Input_eq }

noncomputable def innerPair360Data : WideLogData :=
  { lower := endpoint93
    upper := endpoint469 }

noncomputable def innerPair360Input : RationalEnclosure :=
  { lower := (8485923/8388608), upper := (17534265/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair360Input_eq :
    innerPair360Input = outerEnclosure 24 innerPair360Data.output := by
  rfl'

theorem innerPair360RoundedFacts :
    InnerPairRoundedFacts innerPair360Data innerPair360Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair360Input_eq }

noncomputable def innerPair361Data : WideLogData :=
  { lower := endpoint94
    upper := endpoint95 }

noncomputable def innerPair361Input : RationalEnclosure :=
  { lower := (7580885/8388608), upper := (4072735/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair361Input_eq :
    innerPair361Input = outerEnclosure 24 innerPair361Data.output := by
  rfl'

theorem innerPair361RoundedFacts :
    InnerPairRoundedFacts innerPair361Data innerPair361Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair361Input_eq }

noncomputable def innerPair362Data : WideLogData :=
  { lower := endpoint94
    upper := endpoint419 }

noncomputable def innerPair362Input : RationalEnclosure :=
  { lower := (7580885/8388608), upper := (3869335/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair362Input_eq :
    innerPair362Input = outerEnclosure 24 innerPair362Data.output := by
  rfl'

theorem innerPair362RoundedFacts :
    InnerPairRoundedFacts innerPair362Data innerPair362Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair362Input_eq }

noncomputable def innerPair363Data : WideLogData :=
  { lower := endpoint94
    upper := endpoint434 }

noncomputable def innerPair363Input : RationalEnclosure :=
  { lower := (7580885/8388608), upper := (1947653/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair363Input_eq :
    innerPair363Input = outerEnclosure 24 innerPair363Data.output := by
  rfl'

theorem innerPair363RoundedFacts :
    InnerPairRoundedFacts innerPair363Data innerPair363Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair363Input_eq }

noncomputable def innerPair364Data : WideLogData :=
  { lower := endpoint94
    upper := endpoint436 }

noncomputable def innerPair364Input : RationalEnclosure :=
  { lower := (7580885/8388608), upper := (3997611/4194304) }

set_option maxRecDepth 1000000 in
private theorem innerPair364Input_eq :
    innerPair364Input = outerEnclosure 24 innerPair364Data.output := by
  rfl'

theorem innerPair364RoundedFacts :
    InnerPairRoundedFacts innerPair364Data innerPair364Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair364Input_eq }

noncomputable def innerPair365Data : WideLogData :=
  { lower := endpoint95
    upper := endpoint451 }

noncomputable def innerPair365Input : RationalEnclosure :=
  { lower := (8145469/8388608), upper := (16683407/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair365Input_eq :
    innerPair365Input = outerEnclosure 24 innerPair365Data.output := by
  rfl'

theorem innerPair365RoundedFacts :
    InnerPairRoundedFacts innerPair365Data innerPair365Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair365Input_eq }

noncomputable def innerPair366Data : WideLogData :=
  { lower := endpoint95
    upper := endpoint461 }

noncomputable def innerPair366Input : RationalEnclosure :=
  { lower := (8145469/8388608), upper := (8390053/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair366Input_eq :
    innerPair366Input = outerEnclosure 24 innerPair366Data.output := by
  rfl'

theorem innerPair366RoundedFacts :
    InnerPairRoundedFacts innerPair366Data innerPair366Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair366Input_eq }

noncomputable def innerPair367Data : WideLogData :=
  { lower := endpoint96
    upper := endpoint97 }

noncomputable def innerPair367Input : RationalEnclosure :=
  { lower := (8674439/8388608), upper := (17717625/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair367Input_eq :
    innerPair367Input = outerEnclosure 24 innerPair367Data.output := by
  rfl'

theorem innerPair367RoundedFacts :
    InnerPairRoundedFacts innerPair367Data innerPair367Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair367Input_eq }

noncomputable def innerPair368Data : WideLogData :=
  { lower := endpoint96
    upper := endpoint98 }

noncomputable def innerPair368Input : RationalEnclosure :=
  { lower := (8674439/8388608), upper := (18078439/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair368Input_eq :
    innerPair368Input = outerEnclosure 24 innerPair368Data.output := by
  rfl'

theorem innerPair368RoundedFacts :
    InnerPairRoundedFacts innerPair368Data innerPair368Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair368Input_eq }

noncomputable def innerPair369Data : WideLogData :=
  { lower := endpoint96
    upper := endpoint99 }

noncomputable def innerPair369Input : RationalEnclosure :=
  { lower := (8674439/8388608), upper := (2303957/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair369Input_eq :
    innerPair369Input = outerEnclosure 24 innerPair369Data.output := by
  rfl'

theorem innerPair369RoundedFacts :
    InnerPairRoundedFacts innerPair369Data innerPair369Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair369Input_eq }

noncomputable def innerPair370Data : WideLogData :=
  { lower := endpoint96
    upper := endpoint470 }

noncomputable def innerPair370Input : RationalEnclosure :=
  { lower := (8674439/8388608), upper := (8904279/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair370Input_eq :
    innerPair370Input = outerEnclosure 24 innerPair370Data.output := by
  rfl'

theorem innerPair370RoundedFacts :
    InnerPairRoundedFacts innerPair370Data innerPair370Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair370Input_eq }

noncomputable def innerPair371Data : WideLogData :=
  { lower := endpoint97
    upper := endpoint98 }

noncomputable def innerPair371Input : RationalEnclosure :=
  { lower := (17717623/16777216), upper := (18078439/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair371Input_eq :
    innerPair371Input = outerEnclosure 24 innerPair371Data.output := by
  rfl'

theorem innerPair371RoundedFacts :
    InnerPairRoundedFacts innerPair371Data innerPair371Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair371Input_eq }

noncomputable def innerPair372Data : WideLogData :=
  { lower := endpoint97
    upper := endpoint99 }

noncomputable def innerPair372Input : RationalEnclosure :=
  { lower := (17717623/16777216), upper := (2303957/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair372Input_eq :
    innerPair372Input = outerEnclosure 24 innerPair372Data.output := by
  rfl'

theorem innerPair372RoundedFacts :
    InnerPairRoundedFacts innerPair372Data innerPair372Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair372Input_eq }

noncomputable def innerPair373Data : WideLogData :=
  { lower := endpoint97
    upper := endpoint472 }

noncomputable def innerPair373Input : RationalEnclosure :=
  { lower := (17717623/16777216), upper := (18167443/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair373Input_eq :
    innerPair373Input = outerEnclosure 24 innerPair373Data.output := by
  rfl'

theorem innerPair373RoundedFacts :
    InnerPairRoundedFacts innerPair373Data innerPair373Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair373Input_eq }

noncomputable def innerPair374Data : WideLogData :=
  { lower := endpoint97
    upper := endpoint482 }

noncomputable def innerPair374Input : RationalEnclosure :=
  { lower := (17717623/16777216), upper := (18777591/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair374Input_eq :
    innerPair374Input = outerEnclosure 24 innerPair374Data.output := by
  rfl'

theorem innerPair374RoundedFacts :
    InnerPairRoundedFacts innerPair374Data innerPair374Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair374Input_eq }

noncomputable def innerPair375Data : WideLogData :=
  { lower := endpoint98
    upper := endpoint99 }

noncomputable def innerPair375Input : RationalEnclosure :=
  { lower := (9039219/8388608), upper := (2303957/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair375Input_eq :
    innerPair375Input = outerEnclosure 24 innerPair375Data.output := by
  rfl'

theorem innerPair375RoundedFacts :
    InnerPairRoundedFacts innerPair375Data innerPair375Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair375Input_eq }

noncomputable def innerPair376Data : WideLogData :=
  { lower := endpoint98
    upper := endpoint482 }

noncomputable def innerPair376Input : RationalEnclosure :=
  { lower := (9039219/8388608), upper := (18777591/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair376Input_eq :
    innerPair376Input = outerEnclosure 24 innerPair376Data.output := by
  rfl'

theorem innerPair376RoundedFacts :
    InnerPairRoundedFacts innerPair376Data innerPair376Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair376Input_eq }

noncomputable def innerPair377Data : WideLogData :=
  { lower := endpoint98
    upper := endpoint483 }

noncomputable def innerPair377Input : RationalEnclosure :=
  { lower := (9039219/8388608), upper := (2389567/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair377Input_eq :
    innerPair377Input = outerEnclosure 24 innerPair377Data.output := by
  rfl'

theorem innerPair377RoundedFacts :
    InnerPairRoundedFacts innerPair377Data innerPair377Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair377Input_eq }

noncomputable def innerPair378Data : WideLogData :=
  { lower := endpoint98
    upper := endpoint491 }

noncomputable def innerPair378Input : RationalEnclosure :=
  { lower := (9039219/8388608), upper := (18518811/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair378Input_eq :
    innerPair378Input = outerEnclosure 24 innerPair378Data.output := by
  rfl'

theorem innerPair378RoundedFacts :
    InnerPairRoundedFacts innerPair378Data innerPair378Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair378Input_eq }

noncomputable def innerPair379Data : WideLogData :=
  { lower := endpoint98
    upper := endpoint493 }

noncomputable def innerPair379Input : RationalEnclosure :=
  { lower := (9039219/8388608), upper := (9345887/8388608) }

set_option maxRecDepth 1000000 in
private theorem innerPair379Input_eq :
    innerPair379Input = outerEnclosure 24 innerPair379Data.output := by
  rfl'

theorem innerPair379RoundedFacts :
    InnerPairRoundedFacts innerPair379Data innerPair379Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair379Input_eq }

noncomputable def innerPair380Data : WideLogData :=
  { lower := endpoint98
    upper := endpoint529 }

noncomputable def innerPair380Input : RationalEnclosure :=
  { lower := (9039219/8388608), upper := (1153343/1048576) }

set_option maxRecDepth 1000000 in
private theorem innerPair380Input_eq :
    innerPair380Input = outerEnclosure 24 innerPair380Data.output := by
  rfl'

theorem innerPair380RoundedFacts :
    InnerPairRoundedFacts innerPair380Data innerPair380Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair380Input_eq }

noncomputable def innerPair381Data : WideLogData :=
  { lower := endpoint99
    upper := endpoint482 }

noncomputable def innerPair381Input : RationalEnclosure :=
  { lower := (18431655/16777216), upper := (18777591/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair381Input_eq :
    innerPair381Input = outerEnclosure 24 innerPair381Data.output := by
  rfl'

theorem innerPair381RoundedFacts :
    InnerPairRoundedFacts innerPair381Data innerPair381Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair381Input_eq }

noncomputable def innerPair382Data : WideLogData :=
  { lower := endpoint99
    upper := endpoint483 }

noncomputable def innerPair382Input : RationalEnclosure :=
  { lower := (18431655/16777216), upper := (2389567/2097152) }

set_option maxRecDepth 1000000 in
private theorem innerPair382Input_eq :
    innerPair382Input = outerEnclosure 24 innerPair382Data.output := by
  rfl'

theorem innerPair382RoundedFacts :
    InnerPairRoundedFacts innerPair382Data innerPair382Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair382Input_eq }

noncomputable def innerPair383Data : WideLogData :=
  { lower := endpoint99
    upper := endpoint484 }

noncomputable def innerPair383Input : RationalEnclosure :=
  { lower := (18431655/16777216), upper := (19448769/16777216) }

set_option maxRecDepth 1000000 in
private theorem innerPair383Input_eq :
    innerPair383Input = outerEnclosure 24 innerPair383Data.output := by
  rfl'

theorem innerPair383RoundedFacts :
    InnerPairRoundedFacts innerPair383Data innerPair383Input :=
  { coversLogInner :=
      covers_of_outerEnclosure_eq 24 innerPair383Input_eq }

end LRSmallSWideLogRoundedScalarV2
end CourtadeKumar
